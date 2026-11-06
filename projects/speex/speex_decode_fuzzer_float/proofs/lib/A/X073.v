(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X000 X04b X07z X05o X05s X09j X05l
X071 X06v X06y X06u.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0wl X106 X0xn X0xq X0xm.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Section Kit.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation usp := (x_usp X). Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X).
Local Notation sf := (x_sf X). Local Notation mR := (x_mR X).

Lemma hx_arith :
368 <= usp /\ usp + 16 <= USTACK_TOP /\ usp mod 16 = 0 /\ S1 mod 32 = 0 /\ usp - 368 <= S1 <= usp - 352
/\ x_sp0 X - STACK_WIN <= lo /\ lo + RT_STACK + H_STACK <= S1 /\ SH_HI <= lo
/\ 0 < F /\ F mod 64 = 0 /\ F + 16384 <= lo /\ SEGTOP_A <= F
/\ sf = shad F /\ shad (F + 16384) = sf + 2048 /\ SH_LO <= sf /\ sf + 2048 <= SH_HI /\ (F + 16384 <= sf \/ sf + 2048 <= F).
Proof using HX.
destruct HX as [(U16 & U336 & UT) (ES1 & S32 & SR) (LW & LR & SHL) (F0 & F64 & FL & FH & FI) _ _ _ _ _ _ _ _ _ _ _ _ _].
change (fs_size 8) with 16384 in *.
assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
assert (ESF : sf = shad F) by (unfold x_sf; rewrite shad_shiftr; reflexivity).
destruct (shad_range_al F 16384 ltac:(lia) F8 ltac:(reflexivity) ltac:(lia) ltac:(clear - FL LR SR UT; unfold RT_STACK, H_STACK, APP_TOP, USTACK_TOP in *; lia)) as (A1 & A2).
change (16384 / 8) with 2048 in A2.
assert (SA : shad (F + 16384) = shad F + 2048) by (rewrite (shad_aligned_add F 16384 F8 ltac:(lia)); reflexivity).
do 11 (split; [assumption|]). split; [unfold SEGTOP_A in *; lia|].
split; [exact ESF|]. split; [rewrite SA, ESF; reflexivity|]. split; [rewrite ESF; exact A1|]. split; [rewrite ESF; exact A2|].
rewrite ESF. destruct FH as [H|H]; [left| right]; unfold SH_LO, SH_HI in *; lia.
Qed.

Ltac hx_facts :=
let U336 := fresh "U336" in let UT := fresh "UT" in let U16 := fresh "U16" in let S32 := fresh "S32" in let SR := fresh "SR" in
let LW := fresh "LW" in let LR := fresh "LR" in let SHL := fresh "SHL" in let FP0 := fresh "FP0" in let F64 := fresh "F64" in
let FL := fresh "FL" in let FI := fresh "FI" in let ESF := fresh "ESF" in let ESF2 := fresh "ESF" in let SH1 := fresh "SH1" in let SH2 := fresh "SH2" in
let FSA := fresh "FSA" in
destruct hx_arith as (U336 & UT & U16 & S32 & SR & LW & LR & SHL & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).

Lemma h_out_WL_stack : forall x, S1 + 248 <= x -> x < USTACK_TOP -> outside (h_WL IO_FP X) x.
Proof using HX IO_img.
intros x H1 H2. hx_facts. unfold h_WL. cbn [outside].
split; [lia|]. split; [unfold SH_HI, RT_STACK, H_STACK in *; lia|]. split; [unfold RT_STACK, H_STACK in *; lia|].
apply (outside_img IO_FP x IO_img). right. unfold SEGTOP_A, SH_HI, RT_STACK, H_STACK in *. lia.
Qed.
Lemma h_out_WL_rshadow : forall x, sf + 16 <= x < sf + 2048 -> outside (h_WL IO_FP X) x.
Proof using HX IO_img.
intros x Hx. hx_facts. unfold h_WL. cbn [outside].
split; [unfold SH_HI, RT_STACK, H_STACK in *; lia|]. split; [lia|]. split; [destruct FSA; lia|].
apply (outside_img IO_FP x IO_img). right. unfold SEGTOP_A, SH_LO in *. lia.
Qed.
Lemma h_out_WL_fhdr : forall x, F <= x < F + 32 -> outside (h_WL IO_FP X) x.
Proof using HX IO_img.
intros x Hx. hx_facts. unfold h_WL. cbn [outside].
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [destruct FSA; lia|]. split; [lia|].
apply (outside_img IO_FP x IO_img). right. lia.
Qed.

Section AtM.
Variable m : mem.
Hypothesis PF : rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m.

Lemma h_shr_at : rw_cells bsegs m (sf + 16) [CB 1144 HSH_R].
Proof using HX IO_img PF.
pose proof (hi_shr _ _ _ HX) as B. hx_facts.
apply (rw_cells_agree_nw bsegs mR m _ _ B). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
split; [right; right; right; right; exists F, 8%nat; split; [left; reflexivity|]; change (fs_size 8) with 16384; rewrite <- ESF, ESF0; lia|].
apply h_out_WL_rshadow. lia.
Qed.

Lemma h_acc_at :
acc bsegs m (F + HO_OUT) 8000 /\ acc bsegs m (F + HO_FSZ) 4 /\ acc bsegs m (F + HO_BITS) BITS_SIZEOF /\ acc bsegs m (F + HO_OY) 32
/\ acc bsegs m (F + HO_OG) 32 /\ acc bsegs m (F + HO_OP) 48 /\ acc bsegs m (F + HO_OS) 408 /\ acc bsegs m (F + HO_STEREO) 24
/\ acc bsegs m (F + HO_RATE) 4 /\ acc bsegs m (F + HO_LOOK) 4.
Proof using HX IO_img PF.
pose proof h_shr_at as B. hx_facts. rewrite ESF in B. destruct B as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
apply (hsh_R_acc m F); [clear - F64; Z.div_mod_to_equations; lia| lia| exact B].
Qed.

Lemma h_saves_at : rw_cells bsegs m (usp + -104) (h_saves (x_s11 X) (x_s10 X) (x_s9 X) (x_s8 X) (x_s7 X) (x_s6 X) (x_s5 X) (x_s4 X) (x_s3 X) (x_s2 X) (x_s1 X) (x_s0 X) (x_ra X)).
Proof using HX IO_img PF.
pose proof (hi_saves _ _ _ HX) as SV. hx_facts.
apply (rw_cells_agree_nw bsegs mR m _ _ SV). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. cbn [cells_size csize h_saves Nat.add] in Hx.
split; [left; unfold USTACK_TOP in *; lia|]. apply h_out_WL_stack; [lia| unfold USTACK_TOP in *; lia].
Qed.

Lemma h_gap_at : exists jg, rw_cells bsegs m (S1 + 248) [CB (Z.to_nat (usp - 352 - S1)) jg].
Proof using HX IO_img PF.
destruct (hi_gap _ _ _ HX) as (jg & GP). hx_facts. exists jg.
apply (rw_cells_agree_nw bsegs mR m _ _ GP). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
rewrite Nat.add_0_r, Z2Nat.id in Hx by lia.
split; [left; unfold USTACK_TOP in *; lia|]. apply h_out_WL_stack; [lia| unfold USTACK_TOP in *; lia].
Qed.

Lemma h_hdr_at : rw_cells bsegs m F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 HF_DESC); C8 (Z_to_bv 64 A_LLVMFuzzerTestOneInput)].
Proof using HX IO_img PF.
pose proof (hi_hdr _ _ _ HX) as HD. hx_facts.
apply (rw_cells_agree_nw bsegs mR m _ _ HD). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
split; [right; right; right; left; exists F, 8%nat; split; [left; reflexivity|]; change (fs_size 8) with 16384; lia|].
apply h_out_WL_fhdr. lia.
Qed.

Lemma h_payload_at : bytes_at bsegs m (x_d X) (x_bs X).
Proof using HX IO_img PF.
destruct (hi_pay _ _ _ HX) as (D0 & SZ & BY & PAY). hx_facts.
destruct PAY as [(p & n & INP & P1 & P2) | E]; [| rewrite E in *; apply bytes_at_nil; lia].
destruct (hi_live_geo _ _ _ HX p n INP) as (G1 & G2 & G3).
apply (bytes_at_agree bsegs mR m _ _ BY). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. unfold x_size in P2.
split; [right; right; left; exists p, n; split; [exact INP| lia]|].
assert (NAX : ~ (F <= x < F + 16384) /\ ~ (sf <= x < sf + 2048)).
{ apply (hi_naf _ _ _ HX). right; right; left. exists p, n. split; [exact INP| lia]. }
unfold h_WL. cbn [outside]. destruct NAX as (N1 & N2).
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [lia|]. split; [lia|].
apply (outside_img IO_FP x IO_img). unfold SEGTOP_A in *. destruct G3; lia.
Qed.
End AtM.

Lemma h_pf_entry : forall m, rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> rt_pres_fp (x_live X) [] usp IO_FP (x_m0 X) m.
Proof using HX IO_img.
intros m PF. pose proof (hi_pf0 _ _ _ HX) as PF0. hx_facts.
apply (pres_fp_trans _ _ _ _ (x_m0 X) mR m PF0).
intros a Ha Ho. apply PF.
- destruct Ha as [H|[H|[H|[H|H]]]].
+ left. lia.
+ right; left. exact H.
+ right; right; left. exact H.
+ destruct H as (f & k & [] & _).
+ destruct H as (f & k & [] & _).
- pose proof (hi_naf _ _ _ HX (bv_unsigned a) Ha) as (N1 & N2).
unfold h_WL. cbn [outside]. split; [| split; [lia| split; [lia| exact Ho]]].
destruct Ha as [H|[H|[H|[H|H]]]].
+ unfold RT_STACK, H_STACK in *. lia.
+ pose proof (client_static_range _ H). unfold SEGTOP_A, RT_STACK, H_STACK, SH_HI in *. lia.
+ destruct H as (p & n & INP & P1). destruct (hi_live_geo _ _ _ HX p n INP) as (G1 & _). unfold RT_STACK, H_STACK in *. lia.
+ destruct H as (f & k & [] & _).
+ destruct H as (f & k & [] & _).
Qed.
End Kit.

Section KitX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma h_live_nodup : forall (Σ : rts RT) (m : mem) L pre rest, ART RT Σ m -> rt_live RT Σ = pre ++ L ++ rest ->
(forall e, In e L -> 0 < snd e) -> List.NoDup (map fst L).
Proof using AF.
intros Σ m L. induction L as [|[p n] L IH]; intros pre rest ART0 E POS; [constructor|].
cbn [map fst]. constructor.
- intros Hin. apply in_map_iff in Hin. destruct Hin as ([p2 n2] & E2 & Hin). cbn [fst] in E2. subst p2.
pose proof (POS (p, n) ltac:(left; reflexivity)) as P1. pose proof (POS (p, n2) ltac:(right; exact Hin)) as P2. cbn [snd] in P1, P2.
destruct (af_live_disj RT AF Σ m p n p n2 pre (L ++ rest) ART0 E ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hin)); lia.
- apply (IH (pre ++ [(p, n)]) rest ART0); [rewrite <- app_assoc; exact E| intros e He; apply POS; right; exact He].
Qed.
End KitX.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Section Kit.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation usp := (x_usp X). Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X).
Local Notation sf := (x_sf X). Local Notation mR := (x_mR X).

Lemma hx_arith :
336 <= usp /\ usp + 16 <= USTACK_TOP /\ usp mod 16 = 0 /\ S1 mod 32 = 0 /\ usp - 336 <= S1 <= usp - 320
/\ x_sp0 X - STACK_WIN <= lo /\ lo + RT_STACK + H_STACK <= S1 /\ SH_HI <= lo
/\ 0 < F /\ F mod 64 = 0 /\ F + 16384 <= lo /\ SEGTOP_A <= F
/\ sf = shad F /\ shad (F + 16384) = sf + 2048 /\ SH_LO <= sf /\ sf + 2048 <= SH_HI /\ (F + 16384 <= sf \/ sf + 2048 <= F).
Proof using HX.
destruct HX as [(U16 & U336 & UT) (ES1 & S32 & SR) (LW & LR & SHL) (F0 & F64 & FL & FH & FI) _ _ _ _ _ _ _ _ _ _ _ _ _].
change (fs_size 8) with 16384 in *.
assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
assert (ESF : sf = shad F) by (unfold x_sf; rewrite shad_shiftr; reflexivity).
destruct (shad_range_al F 16384 ltac:(lia) F8 ltac:(reflexivity) ltac:(lia) ltac:(clear - FL LR SR UT; unfold RT_STACK, H_STACK, APP_TOP, USTACK_TOP in *; lia)) as (A1 & A2).
change (16384 / 8) with 2048 in A2.
assert (SA : shad (F + 16384) = shad F + 2048) by (rewrite (shad_aligned_add F 16384 F8 ltac:(lia)); reflexivity).
do 11 (split; [assumption|]). split; [unfold IMG_TOP, SEGTOP_A in *; lia|].
split; [exact ESF|]. split; [rewrite SA, ESF; reflexivity|]. split; [rewrite ESF; exact A1|]. split; [rewrite ESF; exact A2|].
rewrite ESF. destruct FH as [H|H]; [left| right]; unfold SH_LO, SH_HI in *; lia.
Qed.

Ltac hx_facts :=
let U336 := fresh "U336" in let UT := fresh "UT" in let U16 := fresh "U16" in let S32 := fresh "S32" in let SR := fresh "SR" in
let LW := fresh "LW" in let LR := fresh "LR" in let SHL := fresh "SHL" in let FP0 := fresh "FP0" in let F64 := fresh "F64" in
let FL := fresh "FL" in let FI := fresh "FI" in let ESF := fresh "ESF" in let ESF2 := fresh "ESF" in let SH1 := fresh "SH1" in let SH2 := fresh "SH2" in
let FSA := fresh "FSA" in
destruct hx_arith as (U336 & UT & U16 & S32 & SR & LW & LR & SHL & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).

Lemma h_out_WL_stack : forall x, S1 + 216 <= x -> x < USTACK_TOP -> outside (h_WL IO_FP X) x.
Proof using HX IO_img.
intros x H1 H2. hx_facts. unfold h_WL. cbn [outside].
split; [lia|]. split; [unfold SH_HI, RT_STACK, H_STACK in *; lia|]. split; [unfold RT_STACK, H_STACK in *; lia|].
apply (outside_img IO_FP x IO_img). right. unfold SEGTOP_A, SH_HI, RT_STACK, H_STACK in *. lia.
Qed.
Lemma h_out_WL_rshadow : forall x, sf + 16 <= x < sf + 2048 -> outside (h_WL IO_FP X) x.
Proof using HX IO_img.
intros x Hx. hx_facts. unfold h_WL. cbn [outside].
split; [unfold SH_HI, RT_STACK, H_STACK in *; lia|]. split; [lia|]. split; [destruct FSA; lia|].
apply (outside_img IO_FP x IO_img). right. unfold SEGTOP_A, SH_LO in *. lia.
Qed.
Lemma h_out_WL_fhdr : forall x, F <= x < F + 32 -> outside (h_WL IO_FP X) x.
Proof using HX IO_img.
intros x Hx. hx_facts. unfold h_WL. cbn [outside].
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [destruct FSA; lia|]. split; [lia|].
apply (outside_img IO_FP x IO_img). right. lia.
Qed.

Section AtM.
Variable m : mem.
Hypothesis PF : rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m.

Lemma h_shr_at : rw_cells asegs m (sf + 16) [CB 1144 HSH_R].
Proof using HX IO_img PF.
pose proof (hi_shr _ _ _ HX) as B. hx_facts.
apply (rw_cells_agree_nw asegs mR m _ _ B). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
split; [right; right; right; right; exists F, 8%nat; split; [left; reflexivity|]; change (fs_size 8) with 16384; rewrite <- ESF, ESF0; lia|].
apply h_out_WL_rshadow. lia.
Qed.

Lemma h_acc_at :
acc asegs m (F + HO_OUT) 8000 /\ acc asegs m (F + HO_FSZ) 4 /\ acc asegs m (F + HO_BITS) BITS_SIZEOF /\ acc asegs m (F + HO_OY) 32
/\ acc asegs m (F + HO_OG) 32 /\ acc asegs m (F + HO_OP) 48 /\ acc asegs m (F + HO_OS) 408 /\ acc asegs m (F + HO_STEREO) 24
/\ acc asegs m (F + HO_RATE) 4 /\ acc asegs m (F + HO_LOOK) 4.
Proof using HX IO_img PF.
pose proof h_shr_at as B. hx_facts. rewrite ESF in B. destruct B as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
apply (hsh_R_acc m F); [clear - F64; Z.div_mod_to_equations; lia| lia| exact B].
Qed.

Lemma h_saves_at : rw_cells asegs m (usp + -104) (h_saves (x_s11 X) (x_s10 X) (x_s9 X) (x_s8 X) (x_s7 X) (x_s6 X) (x_s5 X) (x_s4 X) (x_s3 X) (x_s2 X) (x_s1 X) (x_s0 X) (x_ra X)).
Proof using HX IO_img PF.
pose proof (hi_saves _ _ _ HX) as SV. hx_facts.
apply (rw_cells_agree_nw asegs mR m _ _ SV). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. cbn [cells_size csize h_saves Nat.add] in Hx.
split; [left; unfold USTACK_TOP in *; lia|]. apply h_out_WL_stack; [lia| unfold USTACK_TOP in *; lia].
Qed.

Lemma h_gap_at : exists jg, rw_cells asegs m (S1 + 216) [CB (Z.to_nat (usp - 320 - S1)) jg].
Proof using HX IO_img PF.
destruct (hi_gap _ _ _ HX) as (jg & GP). hx_facts. exists jg.
apply (rw_cells_agree_nw asegs mR m _ _ GP). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
rewrite Nat.add_0_r, Z2Nat.id in Hx by lia.
split; [left; unfold USTACK_TOP in *; lia|]. apply h_out_WL_stack; [lia| unfold USTACK_TOP in *; lia].
Qed.

Lemma h_hdr_at : rw_cells asegs m F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x227f8); C8 (Z_to_bv 64 0x96668)].
Proof using HX IO_img PF.
pose proof (hi_hdr _ _ _ HX) as HD. hx_facts.
apply (rw_cells_agree_nw asegs mR m _ _ HD). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
split; [right; right; right; left; exists F, 8%nat; split; [left; reflexivity|]; change (fs_size 8) with 16384; lia|].
apply h_out_WL_fhdr. lia.
Qed.

Lemma h_payload_at : bytes_at asegs m (x_d X) (x_bs X).
Proof using HX IO_img PF.
destruct (hi_pay _ _ _ HX) as (D0 & SZ & BY & PAY). hx_facts.
destruct PAY as [(p & n & INP & P1 & P2) | E]; [| rewrite E in *; apply bytes_at_nil; lia].
destruct (hi_live_geo _ _ _ HX p n INP) as (G1 & G2 & G3).
apply (bytes_at_agree asegs mR m _ _ BY). apply (agree_of_pres_fp _ _ _ _ mR m _ PF). intros x Hx. unfold x_size in P2.
split; [right; right; left; exists p, n; split; [exact INP| lia]|].
assert (NAX : ~ (F <= x < F + 16384) /\ ~ (sf <= x < sf + 2048)).
{ apply (hi_naf _ _ _ HX). right; right; left. exists p, n. split; [exact INP| lia]. }
unfold h_WL. cbn [outside]. destruct NAX as (N1 & N2).
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [lia|]. split; [lia|].
apply (outside_img IO_FP x IO_img). unfold SEGTOP_A in *. destruct G3; lia.
Qed.
End AtM.

Lemma h_pf_entry : forall m, rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> rt_pres_fp (x_live X) [] usp IO_FP (x_m0 X) m.
Proof using HX IO_img.
intros m PF. pose proof (hi_pf0 _ _ _ HX) as PF0. hx_facts.
apply (pres_fp_trans _ _ _ _ (x_m0 X) mR m PF0).
intros a Ha Ho. apply PF.
- destruct Ha as [H|[H|[H|[H|H]]]].
+ left. lia.
+ right; left. exact H.
+ right; right; left. exact H.
+ destruct H as (f & k & [] & _).
+ destruct H as (f & k & [] & _).
- pose proof (hi_naf _ _ _ HX (bv_unsigned a) Ha) as (N1 & N2).
unfold h_WL. cbn [outside]. split; [| split; [lia| split; [lia| exact Ho]]].
destruct Ha as [H|[H|[H|[H|H]]]].
+ unfold RT_STACK, H_STACK in *. lia.
+ pose proof (client_static_range _ H). unfold SEGTOP_A, RT_STACK, H_STACK, SH_HI in *. lia.
+ destruct H as (p & n & INP & P1). destruct (hi_live_geo _ _ _ HX p n INP) as (G1 & _). unfold RT_STACK, H_STACK in *. lia.
+ destruct H as (f & k & [] & _).
+ destruct H as (f & k & [] & _).
Qed.
End Kit.
