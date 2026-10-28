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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC99.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI0u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC90.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition tho_val (idl nP : Z) (X : lzw_abs) (PIX : list Z) (o : thead_out) : Prop :=
let s := la_s X in let c1 := px PIX s in let c2 := px PIX (s + 1) in
match o with
| THO_eidx => idl <= c1 \/ (s < nP - 1 /\ idl <= c2)
| THO_emitc q => c1 < idl /\ ((s = nP - 1 /\ q = c1) \/ (s + 1 = nP - 1 /\ c2 < idl /\ q = init_child idl X c1 c2 /\ q <> 0))
| THO_timiss a b => a = c1 /\ b = c2
| THO_inner q => c1 < idl /\ c2 < idl /\ q = init_child idl X c1 c2 /\ q <> 0
end.
Ltac val_tac :=
unfold tho_val, init_child, px; cbn [la_TI la_s];
try match goal with D : true = true -> _ = nth _ _ 0 |- _ => specialize (D eq_refl) end;
repeat match goal with D : ?v = nth _ _ 0 |- _ => rewrite <- D end;
repeat match goal with H : ?k = _ * _ + _ |- _ => rewrite <- H end;
repeat match goal with D : ?v = nth _ _ 0 |- _ => rewrite <- D end;
first [ lia | repeat split; lia ].
Ltac mem_eq_ro HF :=
lazymatch type of HF with frame_of _ _ ?m0 (ms_mem ?msx) =>
let EQM := fresh "EQM" in
assert (EQM : ms_mem msx = m0)
by (apply functional_extensionality; intros x; apply HF; intros (rg & Hin & Hrg); cbn in Hin;
repeat (destruct Hin as [<-|Hin]; [cbn in Hrg; lia|]); destruct Hin);
rewrite <- EQM in *; clear EQM HF end.
Ltac aleafX HS HJ HE0 HF o :=
pmkst HS; ppcs;
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- exists regs' md' oo, mkCfg (mkst ?rg _ _ _) ?mdx = _ /\ _ =>
exists rg, mdx, o end;
split; [reflexivity|]; split; [exact HJ|];
split; [ lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after _ E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | first [exact HF | exact (alzw_regs_core_of_fix _ _ HF)] | lia | lia] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after _ E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | first [exact HF | exact (alzw_regs_core_of_fix _ _ HF)] | lia | lia]  end
| split; [| solve [val_tac] ]; unfold tho_post; cbn [la_s la_TI] ].
Ltac aregv HS r :=
let R := fresh "R" in
prreg HS r R; rewrite R; clear R; cbn [ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
unfold w64; rewrite ?unsigned_lit_small by lia; rewrite ?Z.add_0_r;
first [ reflexivity | f_equal; lia | match goal with |- ?g => idtac "AREGV" g end ].
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
Lemma thead_segX : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X (PIX : list Z) (V : lzw_v),
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_head regs cx -> agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
atables_at (mrestrict (w_H W7) memT) cx X -> lzw_inv (z_idl cx) (z_nP cx) X ->
getr regs 23 = w64 (la_s X) -> la_s X < z_nP cx ->
vtabs_at SEGS (mrestrict (w_H W7) memT) cx PIX V -> vinv cx PIX X V ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists regs' md' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + tho_pc o)) memT (seg_rom SEGS)) md' /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT md' 7 /\
alzw_regs_fix regs' cx /\ tho_post cx X (mrestrict (w_H W7) memT) regs' o /\ tho_val (z_idl cx) (z_nP cx) X PIX o).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X PIX V HCX HRG HSEP (HBg & HBi & HBt) HJ HFH HG HSL HSS HFR HT HI H24 Hs (_ & GPIX & _) (_ & LenPIX & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR & _). pose proof HFH as (HFX & H30 & H16). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
assert (HBti : In (z_ti cx, 2 * z_idl cx * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; right; left; reflexivity).
assert (HBlm : In (z_lm cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity).
assert (HBlc : In (z_lc cx, 4096) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity).
assert (HBli : In (z_li cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity).
assert (HBtm : In (z_tm cx, 4098 * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
set (m := mrestrict (w_H W7) memT) in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_bi cx) (z_Li cx) HAR HBi) as (_ & _ & _ & _ & Hbipres & _).
assert (Pimg : forall i, 0 <= i < z_nP cx -> YO0d.present m (z_img cx + i)).
{ intros i Hi. destruct (Hbipres (z_img cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
subst m. destruct (garr8_nthZ SEGS (mrestrict (w_H W7) memT) (z_img cx) PIX s GPIX ltac:(lia) ltac:(lia)) as [HC1 HC1r]. set (m := mrestrict (w_H W7) memT) in *.
set (C1v := nth (Z.to_nat s) PIX 0) in *. assert (DC1 : C1v = nth (Z.to_nat s) PIX 0) by reflexivity. clearbody C1v.
remember (s <? z_nP cx - 1) as two eqn:Htwo.
assert (HC2ex : exists C2v, 0 <= C2v < 256 /\ (two = true -> val_mem SEGS m (z_img cx + s + 1) 1 C2v) /\ (two = true -> C2v = nth (Z.to_nat (s + 1)) PIX 0)).
{ destruct two.
- symmetry in Htwo. apply Z.ltb_lt in Htwo.
destruct (garr8_nthZ SEGS m (z_img cx) PIX (s + 1) GPIX ltac:(lia) ltac:(lia)) as [HC2 HC2r].
exists (nth (Z.to_nat (s + 1)) PIX 0). split; [exact HC2r|]. split; [intros _; replace (z_img cx + s + 1) with (z_img cx + (s + 1)) by lia; exact HC2 | intros _; reflexivity].
- exists 0. split; [lia|]. split; intros X0; discriminate X0. }
destruct HC2ex as (C2v & HC2r & HC2 & DC2).
remember (two && (C1v <? z_idl cx) && (C2v <? z_idl cx)) as ti eqn:Hti.
assert (HtiT : ti = true -> two = true /\ C1v < z_idl cx /\ C2v < z_idl cx).
{ intros ->. symmetry in Hti. apply andb_prop in Hti as [B1 B3]. apply andb_prop in B1 as [B1 B2]. apply Z.ltb_lt in B2. apply Z.ltb_lt in B3. auto. }
assert (HtwoT : two = true -> s < z_nP cx - 1) by (intros ->; symmetry in Htwo; apply Z.ltb_lt in Htwo; exact Htwo).
assert (HtwoF : two = false -> s = z_nP cx - 1) by (intros ->; symmetry in Htwo; apply Z.ltb_ge in Htwo; lia).
remember (C1v * z_idl cx + C2v) as K eqn:HK0.
assert (HKr : 0 <= K <= 255 * 256 + 255).
{ subst K. split; [apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia | lia]|].
assert (C1v * z_idl cx <= 255 * 256) by (apply Z.mul_le_mono_nonneg; lia). lia. }
assert (HTIj : ti = true -> (Z.to_nat K < length TI)%nat /\ 0 <= nth (Z.to_nat K) TI 0 < 4096).
{ intros Ht. destruct (HtiT Ht) as (_ & HC1i & HC2i).
destruct (TI_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) C1v C2v ltac:(lia) HI ltac:(lia) ltac:(lia)) as [T1 T2].
cbn [la_TI] in T1, T2. subst K. exact (conj T1 T2). }
remember (nth (Z.to_nat K) TI 0) as vTI eqn:HvTI.
destruct HT as (ATI & ALM & ALI & ATM).
assert (VTI : ti = true -> val_mem SEGS m (z_ti cx + 2 * K) 2 vTI).
{ intros Ht. destruct (HTIj Ht) as [T1 _]. rewrite HvTI. exact (proj1 (arr16_nthZ SEGS m (z_ti cx) TI K ATI ltac:(lia) T1)). }
assert (HKsz : ti = true -> 2 * K + 2 <= z_tisz cx).
{ intros Ht. destruct (HTIj Ht) as [T1 _]. rewrite LenTI in T1. unfold z_tisz. rewrite <- Z.mul_assoc.
pose proof (Z.mul_nonneg_nonneg (z_idl cx) (z_idl cx) ltac:(lia) ltac:(lia)) as Hii.
assert (K < z_idl cx * z_idl cx) by (apply Z2Nat.inj_lt; [lia | exact Hii | exact T1]). lia. }
remember [Z_to_bv 64 (z_img cx + s); Z_to_bv 64 C1v; Z_to_bv 64 C2v; Z_to_bv 64 K; Z_to_bv 64 (z_ti cx + 2 * K); Z_to_bv 64 vTI] as more eqn:Hmore.
remember (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) as E eqn:HE0. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HE60 : ew E 60 = Z_to_bv 64 (z_img cx + s)) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE61 : ew E 61 = Z_to_bv 64 C1v) by (rewrite HE0; change 61%nat with (60 + 1)%nat; rewrite (AE_more regs _ _ _ _ _ more 1 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE62 : ew E 62 = Z_to_bv 64 C2v) by (rewrite HE0; change 62%nat with (60 + 2)%nat; rewrite (AE_more regs _ _ _ _ _ more 2 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE63 : ew E 63 = Z_to_bv 64 K) by (rewrite HE0; change 63%nat with (60 + 3)%nat; rewrite (AE_more regs _ _ _ _ _ more 3 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE64 : ew E 64 = Z_to_bv 64 (z_ti cx + 2 * K)) by (rewrite HE0; change 64%nat with (60 + 4)%nat; rewrite (AE_more regs _ _ _ _ _ more 4 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE65 : ew E 65 = Z_to_bv 64 vTI) by (rewrite HE0; change 65%nat with (60 + 5)%nat; rewrite (AE_more regs _ _ _ _ _ more 5 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE20. pose proof (AE_idl regs cx lp dp mp regs0 more HFC) as HE25.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE22. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE29.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE32.
rewrite <- HE0 in HE2, HE8, HE20, HE25, HE22, HE29, HE32.
assert (HE24 : ew E 23 = Z_to_bv 64 s) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 23%bv 23) by reflexivity; exact H24).
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (acx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app acx_objs fst snd zz_disj z_tisz z_tmsz z_cap cap] in Hs; lia.
assert (HS : st_ok_pi SEGS VAL E (ss_thead two ti) (restrict (w_H W7) (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_thead. rewrite HE0.
apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_HEAD asr_head false false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros X0; discriminate X0. - intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_head regs cx); [exact HFH | lia | lia | lia].
- destruct two, ti; vm_compute; reflexivity.
- unfold thead_regions. apply Forall_cons.
+ unfold region_ok, timg_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE60, unsigned_lit_small by lia. split; [lia|]. split; [destruct two; lia|]. split; [intros o Ho; lia|].
apply Forall_cons.
{ eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC1]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE61, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
destruct two; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | exact (HC2 eq_refl)]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE62, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
+ destruct ti; [|apply Forall_nil]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl).
apply Forall_cons; [|apply Forall_nil].
apply (region_ok_reg16 _ E m 64 65 false (z_ti cx + 2 * K) vTI HE64 HE65); [lia | lia | | exact (VTI eq_refl) | intros X0; discriminate X0].
destruct (HTIj eq_refl) as [_ T2]. lia.
-
unfold thead_regions. destruct ti.
+ destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl).
cbn [all_disjoint app]; unfold extent_disjoint, timg_region, reg16, actx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE8, HE60, HE64, !unsigned_lit_small by lia.
split; [destruct two; septac HSEP 6%nat 7%nat|]. split; [septac HSEP 1%nat 6%nat | exact I].
+ cbn [all_disjoint app]; unfold extent_disjoint, timg_region, actx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE8, HE60, !unsigned_lit_small by lia. split; [destruct two; septac HSEP 6%nat 7%nat | exact I].
-
unfold thead_regions. destruct ti.
+ destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl).
cbn [all_disjoint app]; unfold extent_disjoint, timg_region, reg16, astk_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE2, HE60, HE64, !unsigned_lit_small by lia. split; [destruct two; lia|]. split; [lia | exact I].
+ cbn [all_disjoint app]; unfold extent_disjoint, timg_region, astk_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE2, HE60, !unsigned_lit_small by lia. split; [destruct two; lia | exact I].
- unfold thead_regions. destruct ti; [|cbn [pairwise_disjoint all_disjoint app]; repeat split].
destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl). destruct two; [|discriminate Htw]. specialize (HtwoT eq_refl).
cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, timg_region, reg16; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite HE60, HE64, !unsigned_lit_small by lia. split; [split; [septac HSEP 1%nat 7%nat | exact I] | split; exact I].
- unfold thead_facts. apply atoms_ok_app; [|apply atoms_ok_app].
+ cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE24, HE60, HE61, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ destruct two; [|exact I]. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE62, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ destruct ti; [|exact I]. destruct (HTIj eq_refl) as [_ T2]. specialize (HKsz eq_refl).
cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE63, HE64, HE65, !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists K; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rti3].
- unfold thead_conds. cbn [conds_ok app]. split; [|split].
+ apply (cond_ltu E 23 0 59 0 s (z_nP cx) HE24 HE29); lia.
+ destruct two.
* specialize (HtwoT eq_refl). apply (cond_ltu E 23 0 59 (-1) s (z_nP cx) HE24 HE29); lia.
* specialize (HtwoF eq_refl). apply (cond_geu E 23 0 59 (-1) s (z_nP cx) HE24 HE29); lia.
+ destruct ti; [|exact I]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). cbn [conds_ok].
split; [apply (cond_ltu E 61 0 25 0 C1v (z_idl cx) HE61 HE25); lia|].
split; [apply (cond_ltu E 62 0 25 0 C2v (z_idl cx) HE62 HE25); lia | exact I].
- unfold thead_alias. cbn [alias_ok app]. split.
+ rewrite (alias_add E 32 23 60 (z_img cx) s HE32 HE24 HE60); [reflexivity | lia | lia | lia].
+ destruct ti; [|exact I]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl). cbn [alias_ok].
split; [rewrite HK0 in HE63; apply (alias_mul_add E 61 25 62 63 C1v (z_idl cx) C2v HE61 HE25 HE62 HE63); lia|].
split; [apply (alias_b2i' E 53 63 64 (z_ti cx) K HE22 HE63 HE64); lia | exact I]. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (SHOK : sh_ok SEGS (SOff 27 0) [] E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS))))) by (unfold sh_ok; apply Forall_nil).
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS))) in HJ.
Local Ltac hobl HJ HBi HBt HBg HE60 HE64 HE20 HE8 vimg vti vctx :=
let L := getLAWS in
match goal with
| |- range_addressable _ (U ?Ex _) (U _ (SOff 60 ?c)) ?len =>
rewrite (U_atom_off Ex 60 vimg c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE60 | lia | lia];
eapply (obl_of_block SEGS _ L _ _ _ _ _ Ex (SOff 27 0) _ len _ _ (proj1 HJ) HBi);
[rewrite (U_atom Ex 27 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE20 | unfold SB; lia] | lia | lia]
| |- range_addressable _ (U ?Ex _) (U _ (SOff 64 0)) ?len =>
rewrite (U_atom Ex 64 vti); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE64 | lia];
eapply (obl_of_block SEGS _ L _ _ _ _ _ Ex (SOff 27 0) _ len _ _ (proj1 HJ) HBt);
[rewrite (U_atom Ex 27 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE20 | unfold SB; lia]
| lia | unfold z_tisz in *; match goal with |- _ <= _ + req_size ?n => pose proof (req_size_pos n ltac:(lia)) end; lia]
| |- range_addressable _ (U ?Ex _) (U _ (SOff 8 ?c)) ?len =>
first [ rewrite (U_atom_off Ex 8 vctx c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE8 | lia | lia]
| rewrite (U_atom Ex 8 vctx); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE8 | lia] ];
eapply (obl_of_block SEGS _ L _ _ _ _ _ Ex (SOff 27 0) _ len _ _ (proj1 HJ) HBg);
[rewrite (U_atom Ex 27 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE20 | unfold SB; lia] | lia | change (req_size 72) with 72; lia]
| |- _ => idtac
end.
destruct ti.
-
destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). destruct two; [|discriminate Htw]. specialize (HtwoT eq_refl). destruct (HTIj eq_refl) as [T1 T2]. specialize (HKsz eq_refl).
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|].
mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
+
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_TIMISS; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_eq_U, (U_atom _ 65 vTI), U_SLit in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE65 | lia]). change (zcanon 0) with 0 in Hc.
apply Z.eqb_eq in Hc.
aleafX HS HJ HE0 HFX (THO_timiss C1v C2v). subst K.
split; [aregv HS (23%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|].
split; [rregU HS (17%bv : bv 5) (C1v * z_idl cx)
ltac:(apply (U_mul_atoms _ 61 25 C1v (z_idl cx)); [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE61 | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE25 | lia | lia]) R17; exact R17|].
split; [aregv HS (11%bv : bv 5)|]. split; [aregv HS (14%bv : bv 5)|].
split; [aregv HS (7%bv : bv 5)|]. split; [aregv HS (30%bv : bv 5)|].
split; [lia|]. split; [lia|]. split; [rewrite <- HvTI; exact Hc|]. split; [lia|]. exact (HC2 eq_refl).
+ rewrite branch_eq_U, (U_atom _ 65 vTI), U_SLit in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE65 | lia]). change (zcanon 0) with 0 in Hc.
assert (HvTInz : vTI <> 0) by (destruct (Z.eqb_spec vTI 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
*
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EMITC; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_geu_U, (U_atom_off _ 23 s 1), (U_atom_off _ 59 (z_nP cx) (-1)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE24 | exact HE29] | lia]).
assert (Hs1 : s + 1 = z_nP cx - 1) by (destruct (Z.ltb_spec (s + 1) (z_nP cx + -1)); [discriminate | lia]). clear Hc.
aleafX HS HJ HE0 HFX (THO_emitc vTI).
split; [aregv HS (23%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|]. split; [lia|]. aregv HS (30%bv : bv 5).
* paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_ISET; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_geu_U, (U_atom_off _ 23 s 1), (U_atom_off _ 59 (z_nP cx) (-1)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE24 | exact HE29] | lia]).
assert (Hs1 : s + 1 < z_nP cx - 1) by (destruct (Z.ltb_spec (s + 1) (z_nP cx + -1)); [lia | discriminate]). clear Hc.
aleafX HS HJ HE0 HFX (THO_inner vTI).
split; [aregv HS (23%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|]. split; [aregv HS (7%bv : bv 5)|]. split; [aregv HS (13%bv : bv 5)|].
split; [aregv HS (16%bv : bv 5) | lia].
- destruct two.
+
specialize (HtwoT eq_refl).
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|].
mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
* paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EIDX; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_geu_U, (U_atom _ 61 C1v), (U_atom _ 25 (z_idl cx)) in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE61 | exact HE25] | lia]).
assert (HCge : z_idl cx <= C1v) by (destruct (Z.ltb_spec C1v (z_idl cx)); [discriminate | lia]). clear Hc.
aleafX HS HJ HE0 HFX THO_eidx. exact I.
* rewrite branch_geu_U, (U_atom _ 61 C1v), (U_atom _ 25 (z_idl cx)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE61 | exact HE25] | lia]).
assert (HC1i : C1v < z_idl cx) by (destruct (Z.ltb_spec C1v (z_idl cx)); [lia | discriminate]). clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|].
mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
-- paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EIDX; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_geu_U, (U_atom _ 62 C2v), (U_atom _ 25 (z_idl cx)) in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE62 | exact HE25] | lia]).
assert (HCge : z_idl cx <= C2v) by (destruct (Z.ltb_spec C2v (z_idl cx)); [discriminate | lia]). clear Hc.
aleafX HS HJ HE0 HFX THO_eidx. exact I.
-- rewrite branch_geu_U, (U_atom _ 62 C2v), (U_atom _ 25 (z_idl cx)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE62 | exact HE25] | lia]).
exfalso. destruct (Z.ltb_spec C2v (z_idl cx)); [|discriminate].
assert (X1 : (C1v <? z_idl cx) = true) by (apply Z.ltb_lt; lia).
rewrite X1 in Hti. cbn in Hti. try (rewrite (proj2 (Z.ltb_lt C2v (z_idl cx))) in Hti by lia). discriminate Hti.
+
specialize (HtwoF eq_refl).
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|].
mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
* paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EIDX; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_geu_U, (U_atom _ 61 C1v), (U_atom _ 25 (z_idl cx)) in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE61 | exact HE25] | lia]).
assert (HCge : z_idl cx <= C1v) by (destruct (Z.ltb_spec C1v (z_idl cx)); [discriminate | lia]). clear Hc.
aleafX HS HJ HE0 HFX THO_eidx. exact I.
* rewrite branch_geu_U, (U_atom _ 61 C1v), (U_atom _ 25 (z_idl cx)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE61 | exact HE25] | lia]).
assert (HC1i : C1v < z_idl cx) by (destruct (Z.ltb_spec C1v (z_idl cx)); [lia | discriminate]). clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EMITC; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
aleafX HS HJ HE0 HFX (THO_emitc C1v).
split; [aregv HS (23%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|]. split; [lia|]. aregv HS (30%bv : bv 5).
Qed.
End S.
End e.
End d.
