(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Definition sh66 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 66 0) (SLit 3)) (SOff 27 0).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ttimiss_facts : list (nat * afact) :=
[ (23%nat, mkAF 1 99999999 0); (15%nat, mkAF 0 255 0); (17%nat, mkAF 0 65280 0); (60%nat, APTR 1); (61%nat, mkAF 0 65535 0); (63%nat, mkAF 0 65535 0);
(64%nat, APTR 1); (65%nat, mkAF 0 4095 0); (66%nat, APTR 0); (67%nat, mkAF 0 255 0); (68%nat, mkAF 0 65535 0) ].
Definition ttimiss_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 58 0) (SAlu ALU_SLL (SOff 33 0) (SLit 1)), SOff 60 0);
(SAlu ALU_ADD (SOff 17 0) (SOff 67 0), SOff 68 0);
(SAlu ALU_ADD (SOff 53 0) (SAlu ALU_SLL (SOff 68 0) (SLit 1)), SOff 64 0) ].
Definition ttimiss_pix : YP09.region := YP09.mkRegion (Some 66%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 67 0))].
Definition ttimiss_conds (full : bool) : list acond :=
[ mkAC (if full then BC_NE else BC_EQ) (SAlu ALU_SRL (SOff 34 0) (SLit 12)) (SLit 0); mkAC BC_LTU (SOff 23 0) (SOff 59 0) ].
Definition ttimiss_regions (full : bool) : smem := [ld4 60 61 63; reg16 64 65 (negb full); ttimiss_pix].
Definition ss_ttimiss0 (full : bool) : sstate :=
alzw_ss PC_TIMISS asr_t5 true false (ttimiss_regions full) ttimiss_facts (ttimiss_conds full) ttimiss_alias.
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma ttimiss_seg : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X c1 c2,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_fix regs cx -> getr regs 30 = w64 (z_ctx cx + 60) -> agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
atables_at (mrestrict (w_H W7) memT) cx X -> lzw_inv (z_idl cx) (z_nP cx) X ->
getr regs 23 = w64 (la_s X + 1) -> getr regs 15 = w64 c1 -> getr regs 17 = w64 (c1 * z_idl cx) ->
getr regs 11 = w64 (z_img cx + la_s X + 1) ->
getr regs 14 = alu64 ALU_ADD (alu64 ALU_SRL (w64 (z_img cx + la_s X + 1)) (w64 3)) (w64 SB) ->
getr regs 7 = w64 (z_ti cx) ->
0 <= c1 < z_idl cx -> 0 <= c2 < z_idl cx -> nth (Z.to_nat (c1 * z_idl cx + c2)) (la_TI X) 0 = 0 -> la_s X + 1 < z_nP cx ->
val_mem SEGS (mrestrict (w_H W7) memT) (z_img cx + la_s X + 1) 1 c2 ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists regs' mem' md' X' (full : bool),
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (if full then PC_RST1 else atail_pc cx X'))) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
aabove_eq cx (mrestrict (w_H W7) memT) (mrestrict (w_H W7) mem') /\
if full then arst_pre true cx X (la_s X + 1) regs' (mrestrict (w_H W7) mem')
else atail_post cx X regs' (mrestrict (w_H W7) mem') X').
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X c1 c2 HCX HRG HSEP (HBg & HBi & HBt) HTOK HJ HFX H30 HG HSL HSS HFR HT HI H24 H13 H17 H11 H14 H7 Hc1 Hc2 HTI0 Hs1 HC2.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR & _). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
assert (HBti : In (z_ti cx, 2 * z_idl cx * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; right; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ld cx) _ HAR HBld) as (_ & _ & Hldceil & _ & Hldpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ti cx) _ HAR HBti) as (_ & _ & _ & _ & Htipres & _).
pose proof (req_size_pos (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ltac:(pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)); unfold lzw_MR; lia)) as Hrqld.
pose proof (req_size_pos (2 * z_idl cx * z_idl cx) ltac:(lia)) as Hrqti.
assert (Actx : forall blc lyq i, In (z_ctx cx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ctx cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ctx cx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]. }
assert (Ald : forall blc lyq i, In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) blc -> 0 <= i < req_size (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ->
awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ld cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ld cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; left; reflexivity)); [exact Hb | exact Hi]. }
assert (Ati : forall blc lyq i, In (z_ti cx, 2 * z_idl cx * z_idl cx) blc -> 0 <= i < req_size (2 * z_idl cx * z_idl cx) ->
awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ti cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ti cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; right; left; reflexivity)); [exact Hb | exact Hi]. }
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
remember (c1 * z_idl cx + c2) as K eqn:HK0.
assert (HKr : 0 <= c1 * z_idl cx <= 255 * 256).
{ split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]. }
assert (HKlen : (Z.to_nat K < length TI)%nat /\ 2 * K + 2 <= z_tisz cx).
{ destruct (TI_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) c1 c2 ltac:(lia) HI ltac:(lia) ltac:(lia)) as [T1 _].
cbn [la_TI] in T1. rewrite <- HK0 in T1. split; [exact T1|]. rewrite LenTI in T1. unfold z_tisz.
assert (K < z_idl cx * z_idl cx) by (apply Z2Nat.inj_lt; [lia | nia | exact T1]). nia. }
destruct HKlen as [HKlen HKsz].
set (m := mrestrict (w_H W7) memT) in *.
assert (Pld : forall i, 0 <= i < 2 * (z_nP cx + 2 + z_MR cx) -> YO0d.present m (z_ld cx + i)).
{ intros i Hi. destruct (Hldpres (z_ld cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem2 SEGS m (z_ld cx + 2 * lp)) as (vLD & HvLDr & HvLD); [apply Pld; lia | replace (z_ld cx + 2 * lp + 1) with (z_ld cx + (2 * lp + 1)) by lia; apply Pld; lia |].
destruct (val_mem2 SEGS m (z_ld cx + 2 * lp + 2)) as (vLD1 & HvLD1r & HvLD1);
[replace (z_ld cx + 2 * lp + 2) with (z_ld cx + (2 * lp + 2)) by lia; apply Pld; lia | replace (z_ld cx + 2 * lp + 2 + 1) with (z_ld cx + (2 * lp + 3)) by lia; apply Pld; lia |].
change (2 ^ 16) with 65536 in HvLDr, HvLD1r.
destruct HT as (ATI & ALM & ALI & ATM).
assert (VTI : val_mem SEGS m (z_ti cx + 2 * K) 2 0).
{ rewrite <- HTI0. exact (proj1 (arr16_nthZ SEGS m (z_ti cx) TI K ATI ltac:(lia) HKlen)). }
remember [Z_to_bv 64 (z_ld cx + 2 * lp); Z_to_bv 64 vLD; Z_to_bv 64 0; Z_to_bv 64 vLD1; Z_to_bv 64 (z_ti cx + 2 * K); Z_to_bv 64 0;
Z_to_bv 64 (z_img cx + s + 1); Z_to_bv 64 c2; Z_to_bv 64 K] as more eqn:Hmore.
remember (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) as E eqn:HE0. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HE60 : ew E 60 = Z_to_bv 64 (z_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE61 : ew E 61 = Z_to_bv 64 vLD) by (rewrite HE0; change 61%nat with (60 + 1)%nat; rewrite (AE_more regs _ _ _ _ _ more 1 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE63 : ew E 63 = Z_to_bv 64 vLD1) by (rewrite HE0; change 63%nat with (60 + 3)%nat; rewrite (AE_more regs _ _ _ _ _ more 3 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE64 : ew E 64 = Z_to_bv 64 (z_ti cx + 2 * K)) by (rewrite HE0; change 64%nat with (60 + 4)%nat; rewrite (AE_more regs _ _ _ _ _ more 4 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE65 : ew E 65 = Z_to_bv 64 0) by (rewrite HE0; change 65%nat with (60 + 5)%nat; rewrite (AE_more regs _ _ _ _ _ more 5 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE66 : ew E 66 = Z_to_bv 64 (z_img cx + s + 1)) by (rewrite HE0; change 66%nat with (60 + 6)%nat; rewrite (AE_more regs _ _ _ _ _ more 6 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE67 : ew E 67 = Z_to_bv 64 c2) by (rewrite HE0; change 67%nat with (60 + 7)%nat; rewrite (AE_more regs _ _ _ _ _ more 7 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE68 : ew E 68 = Z_to_bv 64 K) by (rewrite HE0; change 68%nat with (60 + 8)%nat; rewrite (AE_more regs _ _ _ _ _ more 8 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE27. pose proof (AE_ld regs cx lp dp mp regs0 more) as HE58.
pose proof (AE_nP regs cx lp dp mp regs0 more) as HE59. pose proof (AE_lp regs cx lp dp mp regs0 more) as HE33.
pose proof (AE_dp regs cx lp dp mp regs0 more) as HE34. pose proof (AE_mp regs cx lp dp mp regs0 more) as HE35.
pose proof (AE_idl regs cx lp dp mp regs0 more HFC) as HE25. pose proof (AE_ti regs cx lp dp mp regs0 more) as HE53.
rewrite <- HE0 in HE2, HE8, HE27, HE58, HE59, HE33, HE34, HE35, HE25, HE53.
assert (HE23 : ew E 23 = Z_to_bv 64 (s + 1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 23%bv 23) by reflexivity; exact H24).
assert (HE15 : ew E 15 = Z_to_bv 64 c1) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 15%bv 15) by reflexivity; exact H13).
assert (HE17 : ew E 17 = Z_to_bv 64 (c1 * z_idl cx)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 17%bv 17) by reflexivity; exact H17).
remember (dp =? 4096) as full eqn:Hfull.
assert (HS1 : st_ok_pi SEGS VAL E (ss_ttimiss0 full) (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) m (seg_rom SEGS))).
{ unfold ss_ttimiss0. rewrite HE0. apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_TIMISS asr_t5 true false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros _ a Ha. apply (apresent_writable SEGS). apply (proj1 (Hcpres a ltac:(lia))).
- intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_t5 regs cx); [exact HFX | exact H30 | lia | lia].
- destruct full; vm_compute; reflexivity.
- unfold ttimiss_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (region_ok_ld4 E m 60 61 63 (z_ld cx + 2 * lp) vLD vLD1 HE60 HE61 HE63); [lia | lia | lia | lia | exact HvLD | exact HvLD1 |].
intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hldpres (z_ld cx + 2 * lp + o) ltac:(lia))).
+ apply (region_ok_reg16 _ E m 64 65 (negb full) (z_ti cx + 2 * K) 0 HE64 HE65); [lia | lia | lia | exact VTI |].
intros _ o Ho. apply (apresent_writable SEGS). apply (proj1 (Htipres (z_ti cx + 2 * K + o) ltac:(lia))).
+ unfold region_ok, ttimiss_pix. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE66, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC2]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE67, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
- unfold ttimiss_regions. cbn [all_disjoint app]; unfold extent_disjoint, ld4, reg16, ttimiss_pix, actx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE8, HE60, HE64, HE66, !unsigned_lit_small by lia.
split; [septac HSEP 0%nat 6%nat; lia|]. split; [septac HSEP 1%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia | exact I].
- unfold ttimiss_regions. cbn [all_disjoint app]; unfold extent_disjoint, ld4, reg16, ttimiss_pix, astk_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE2, HE60, HE64, HE66, !unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [lia | exact I].
- unfold ttimiss_regions. cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, ld4, reg16, ttimiss_pix; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite HE60, HE64, HE66, !unsigned_lit_small by lia.
split; [split; [septac HSEP 0%nat 1%nat; lia | split; [septac HSEP 0%nat 7%nat; lia | exact I]]|].
split; [split; [septac HSEP 1%nat 7%nat; lia | exact I] | split; exact I].
- unfold ttimiss_facts. cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE23, HE15, HE17, HE60, HE61, HE63, HE64, HE65, HE66, HE67, HE68, !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
+ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
+ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists K; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rti3].
- unfold ttimiss_conds. cbn [conds_ok]. split; [|split; [apply (cond_ltu E 23 0 59 0 (s + 1) (z_nP cx) HE23 HE59); lia | exact I]].
destruct full.
+ apply (cond_ne_U E). rewrite (U_dpfull12 E 34 dp HE34), <- Hfull, U_SLit by lia. discriminate.
+ apply (cond_eq_U E). rewrite (U_dpfull12 E 34 dp HE34), <- Hfull, U_SLit by lia. reflexivity.
- unfold ttimiss_alias. cbn [alias_ok]. split; [apply (alias_b2i' E 58 33 60 (z_ld cx) lp HE58 HE33 HE60); lia|].
assert (HE68' : ew E 68 = Z_to_bv 64 (c1 * z_idl cx + c2)) by (rewrite <- HK0; exact HE68).
split; [apply (alias_add E 17 67 68 (c1 * z_idl cx) c2 HE17 HE67 HE68'); lia|].
split; [apply (alias_b2i' E 53 68 64 (z_ti cx) K HE53 HE68 HE64); lia | exact I]. }
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) m (seg_rom SEGS)) 7%bv (SOff 53 0) HS1 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE53, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H7)) as HS2.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) m (seg_rom SEGS)) 11%bv (SOff 66 0) HS2 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE66, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H11)) as HS3.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) m (seg_rom SEGS)) 14%bv sh66 HS3 eq_refl
ltac:(unfold sh66; cbn [sv_denot ms_regs mkst]; rewrite HE66, HE27, !Z.add_0_r, !unsigned_lit_small by lia; rewrite H14; reflexivity)) as HS.
clear HS1 HS2 HS3. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_ttimiss0 alzw_ss] in HS.
change (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) m (seg_rom SEGS)) with (restrict (w_H W7) (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) memT (seg_rom SEGS))) in HS.
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) memT (seg_rom SEGS))) in HJ.
unfold z_tisz in HKsz, Htisz.
Local Ltac houtF HFr E m vctx vld HE8 HE60 :=
lazymatch type of HFr with frame_of _ _ _ ?m' =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (vctx + 60 <= a < vctx + 68) -> ~ (vld <= a < vld + 4) ->
mbyte SEGS m' a = mbyte SEGS m a)
by (intros a Ha Hn1 Hn2; eapply (aframe_mbyte_list E _ _ _ [(vctx + 60, vctx + 68); (0, 0); (vld, vld + 4); (0, 0); (0, 0)] a HFr Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd YP09.r_base YP09.r_wlo YP09.r_whi reg16 ld4 ttimiss_pix negb actx_region base_val]; rewrite ?HE8, ?HE60, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| cbn; repeat split; lia ]);
clear HFr
end.
Local Ltac houtT HFr E m vctx vld vti HE8 HE60 HE64 :=
lazymatch type of HFr with frame_of _ _ _ ?m' =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (vctx + 60 <= a < vctx + 68) -> ~ (vld <= a < vld + 4) -> ~ (vti <= a < vti + 2) ->
mbyte SEGS m' a = mbyte SEGS m a)
by (intros a Ha Hn1 Hn2 Hn3; eapply (aframe_mbyte_list E _ _ _ [(vctx + 60, vctx + 68); (0, 0); (vld, vld + 4); (vti, vti + 2); (0, 0)] a HFr Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd YP09.r_base YP09.r_wlo YP09.r_whi reg16 ld4 ttimiss_pix negb actx_region base_val]; rewrite ?HE8, ?HE60, ?HE64, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| cbn; repeat split; lia ]);
clear HFr
end.
Local Ltac genT HS HE8 HG houttac vctx e60 v60 HE67 e64 v64 HE71 e66 v66 HE73 :=
let HRg := fresh "HRg" in let G8 := fresh "G8" in
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx => pose proof (st_ok_pi_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HRg | st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HRg  end;
cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ ?Ex _ _ =>
assert (G8 : bv_unsigned (ew Ex 8) = vctx) by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE8; apply unsigned_lit_small; lia) end;
eapply (agen_at_upd _ _ _ _ _ _ v60 v64 v66); [exact HG | intros a Ha; houttac a Ha | | |];
[ change 4%nat with (N.to_nat 4); eapply (field_of_region _ _ 8%nat vctx _ _ _ _ _ 60 4%N e60 v60 HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?HE67, ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia ]
| change 2%nat with (N.to_nat 2); eapply (field_of_region _ _ 8%nat vctx _ _ _ _ _ 64 2%N e64 v64 HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?HE71, ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ]
| change 2%nat with (N.to_nat 2); eapply (field_of_region _ _ 8%nat vctx _ _ _ _ _ 66 2%N e66 v66 HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?HE73, ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ] ].
destruct full; shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_TIMISS)) memT (seg_rom SEGS)))).
-
assert (Hdp4096 : dp = 4096) by (symmetry in Hfull; apply Z.eqb_eq in Hfull; exact Hfull).
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_RST1; try (oblk HJ HBld HE60 HE27 (z_ld cx + 2 * lp)); try (oblk HJ HBg HE8 HE27 (z_ctx cx)).
{ awr_tmp 8%nat (z_ctx cx) HE8 Actx HBg. apply awr_ok_cons_ro; [cbn; lia|].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X' full, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA TI LM LI TM s lp dp mp Cn R), true end.
split; [reflexivity|]. split; [exact HJ|].
houtF HFr E m (z_ctx cx) (z_ld cx + 2 * lp) HE8 HE60.
split; [intros a Ha; apply Hout; lia|].
unfold arst_pre. cbv beta iota. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split.
{ eapply (alzw_regs_fix_after _ _ _ _ _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia]. }
split; [aregv HS (30%bv : bv 5)|]. split; [aregv HS (13%bv : bv 5)|]. split; [aregv HS (7%bv : bv 5)|].
split; [genT HS HE8 HG ltac:(fun a Ha => apply Hout; [lia | lia | septac HSEP 0%nat 6%nat; lia]) (z_ctx cx) (SOff 33 1) (lp + 1) HE33 (SOff 25 2) (z_idl cx + 2) HE25 (SLit 1) 1 HE25|].
split.
{ eapply (atables_at_frame m _ cx (mkLA TI LM LI TM s lp dp mp Cn R) (fun a => (z_ctx cx + 60 <= a < z_ctx cx + 68) \/ (z_ld cx + 2 * lp <= a < z_ld cx + 2 * lp + 4)));
[exact (conj ATI (conj ALM (conj ALI ATM))) | exact HI | lia | exact HRG | intros a Ha Hna; apply Hout; [exact Ha | tauto | tauto] | | | |];
cbn beta; intros a Ha; unfold z_tisz, z_tmsz in Ha.
- septac HSEP 0%nat 1%nat. septac HSEP 1%nat 6%nat. lia.
- septac HSEP 0%nat 2%nat. septac HSEP 2%nat 6%nat. lia.
- septac HSEP 0%nat 4%nat. septac HSEP 4%nat 6%nat. lia.
- septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. lia. }
split; [exact HI|]. split; [exact Hdp4096|]. split; [aregv HS (23%bv : bv 5) | lia].
-
assert (Hdplt : dp < 4096) by (symmetry in Hfull; apply Z.eqb_neq in Hfull; lia).
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_HEAD; try (oblk HJ HBti HE64 HE27 (z_ti cx + 2 * K));
try (oblk HJ HBld HE60 HE27 (z_ld cx + 2 * lp)); try (oblk HJ HBg HE8 HE27 (z_ctx cx)); try (oblk HJ HBi HE66 HE27 (z_img cx + s + 1)).
{ awr_tmp 8%nat (z_ctx cx) HE8 Actx HBg. apply awr_ok_cons_ro; [cbn; lia|].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. awr_tmp 64%nat (z_ti cx + 2 * K) HE64 Ati HBti. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X' full, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA (updn TI (Z.to_nat K) dp) LM LI TM (s + 1) (lp + 1) (dp + 1) mp (Cn + 1) R), false end.
split; [unfold atail_pc; cbn [la_s]; replace (s + 1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ|].
houtT HFr E m (z_ctx cx) (z_ld cx + 2 * lp) (z_ti cx + 2 * K) HE8 HE60 HE64.
split; [intros a Ha; apply Hout; lia|].
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx => pose proof (st_ok_pi_region_nth Ex ssx msx 3%nat _ HS eq_refl) as HR3 | st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 3%nat _ HS eq_refl) as HR3  end.
cbn [ms_mem restrict] in HR3.
lazymatch type of HR3 with region_ok _ ?Ex ?mx _ =>
assert (Vnew : val_mem SEGS mx (z_ti cx + 2 * K) 2 dp)
by (rewrite <- (Z.add_0_r (z_ti cx + 2 * K)); change 2%nat with (N.to_nat 2);
eapply (field_of_region _ _ 64%nat (z_ti cx + 2 * K) _ _ _ _ _ 0 2%N _ dp HR3);
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE64; apply unsigned_lit_small; lia | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE34, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ]) end.
clear HR3.
pose proof (inv_ti (z_idl cx) (z_nP cx) Hidl _ c1 c2 s HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hc1 Hc2) as HI'.
cbn [st_ti] in HI'. rewrite <- HK0 in HI'.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split.
{ split; [|split; [aregv HS (30%bv : bv 5) | aregv HS (16%bv : bv 5)]].
eapply (alzw_regs_fix_after _ _ _ _ _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia]. }
split; [genT HS HE8 HG ltac:(fun a Ha => apply Hout; [lia | lia | septac HSEP 0%nat 6%nat; lia | septac HSEP 1%nat 6%nat; lia])
(z_ctx cx) (SOff 33 1) (lp + 1) HE33 (SOff 34 1) (dp + 1) HE34 (SOff 35 0) mp HE35|].
split.
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_upd; [exact ATI | lia | exact HKlen | lia | exact Vnew |].
intros a Ha Hna. rewrite LenTI, Z2Nat.id in Ha by lia.
apply Hout; [lia | septac HSEP 1%nat 6%nat; lia | septac HSEP 0%nat 1%nat; lia | exact Hna].
- eapply arr16_frame; [exact ALM|]. intros a Ha. rewrite LenLM in Ha. cbn in Ha.
apply Hout; [lia | septac HSEP 2%nat 6%nat; lia | septac HSEP 0%nat 2%nat; lia | septac HSEP 1%nat 2%nat; lia].
- eapply arr16_frame; [exact ALI|]. intros a Ha. rewrite LenLI in Ha. cbn in Ha.
apply Hout; [lia | septac HSEP 4%nat 6%nat; lia | septac HSEP 0%nat 4%nat; lia | septac HSEP 1%nat 4%nat; lia].
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply Hout; [lia | septac HSEP 5%nat 6%nat; lia | septac HSEP 0%nat 5%nat; lia | septac HSEP 1%nat 5%nat; lia]. }
split; [exact HI'|]. split; [aregv HS (23%bv : bv 5) | lia].
Qed.
End S.
End c.
End b.
