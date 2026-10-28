(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals Lra.
From Flocq Require Import Core.Raux Core.Defs.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i YI0x YP14 YI08 YI0c YI0f YI0d UI3h
UI3j UI3k UI3l UI3m.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05 YM04 YM01 YM02 YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN07.
Ltac2 sat_vars () := [@API; @STK; @sp0; @FP; @L; @A; @mem0; @md0; @L2; @A2; @md2; @regs0; @palp; @frp; @nln; @imin; @imax; @cidx; @res; @pal; @fr; @mn0; @mn1; @mn2].
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Local Notation segs := ubs2segs.
Local Notation rom := (seg_rom ubs2segs).
Theorem ubs2_ntn : ntn_spec API.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs palp frp nln imin imax cidx n0 pal fr
HJ Hid Hra Hal16 Htp Hbud Hsptop Hfrm Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Hpa Hfa Hii Himax Hlenp Hlenf Hcidx
Hpalp Hpalhi Hfrp Hfrhi Hfr4 Hpalblk Hfrblk Hpfd Hfr1 Hsum Hnln0 Hnln1 Hnln2 Hn0 Rn0.
pose proof HJ as (HH & _ & _ & _ & _ & (_ & _ & Hceil & H63 & Hstw) & _).
pose (mem0 := mem). pose (md0 := md). pose (regs0 := regs).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
assert (HNTN : NTN_STK = 160 + ALLOC_STACK) by reflexivity. assert (HAS : ALLOC_STACK = 8192) by reflexivity.
assert (Hpalv : forall j, (j < length pal)%nat -> 0 <= nth j pal 0 < 256) by (intros j Hj; exact (proj2 (Hpa j Hj))).
assert (Hfrv : forall j, (j < length fr)%nat -> 0 <= nth j fr 0 < 2 ^ 32) by (intros j Hj; exact (proj2 (Hfa j Hj))).
set (spc := spZ regs - 160).
assert (Hblk_rng : forall b m, In (b, m) (blocks Lc Ac) -> 0 < m -> 4096 <= b /\ b + m <= alloc_ceiling).
{ intros b m Hb Hm. destruct (heap_blocks_range _ _ LAWS _ _ _ _ b m HH Hb Hm) as (H1 & H2 & _). split; assumption. }
eapply SR_bind.
{ ltac2:(satvl ntn_p0 using (sat_vars ()) as LEM1); eapply (LEM1 Lc Ac memc mdc HJ Hid Htp Ha0 Ha1 Ha2 Ha3 Ha4 Ha5). }
cbv beta. intros c1 (Lm & Am & regs2 & mem2 & mdm & r & -> & HJ2 & Hid2 & G2 & G8 & G9 & G18 & G19 & G20 & G21 & G4 & G10 & Gk2 & SV2 & Hres & Hkeep2 & Hhi2).
pose (L2 := Lm). pose (A2 := Am). pose (md2 := mdm). pose (res := r).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (K2n : forall k, nln <= k < nln + 2 -> mbyte segs mem2 k = mbyte segs memc k) by (intros k Hk; apply Hhi2; lia).
assert (K2b : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte segs mem2 (b + i) = mbyte segs memc (b + i)) by exact Hkeep2.
destruct Hres as [[-> Hbl] | (Hrnz & Hr16 & (b1 & b2 & Hbl2 & Hblc) & Hwb)].
-
eapply SR_mono.
{ ltac2:(satvl ntn_pfail using (sat_vars ()) as LEM2); eapply (LEM2 fx regs2 mem2 HJ2 G2 G10 SV2). }
cbv beta. intros c2 (regs3 & -> & R2 & R8 & R9 & R18 & R19 & R20 & R21 & R10 & Gk3).
exists fx, Lm, Am, regs3, mem2, mdm, 0.
split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HJ2|]. split; [exact Hid2|].
split.
{ apply regs_preserved_of_list. intros rr Hrr. cbv [CALLEE_SAVED In] in Hrr.
repeat (destruct Hrr as [<-|Hrr]; [first [assumption | lazymatch goal with |- getr _ ?k = _ => rewrite (Gk3 k ltac:(cbv; tauto)); apply (Gk2 k); cbv; tauto end] |]). destruct Hrr. }
split; [exact R10|].
split; [intros a Ha Hna Hnn; apply Hhi2; [exact Ha | subst spc; lia]|].
split; [exact Hkeep2|].
left. split; [reflexivity|]. split; [exact Hbl|].
eapply val_mem_kept; [exact Hn0|]. intros k Hk. apply K2n. cbn in Hk. lia.
-
assert (Hrin : In (r, NODE_SIZE) (blocks Lm Am)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ r NODE_SIZE HH2 Hrin ltac:(rewrite HNS; lia)) as (Hres0 & Hres1 & _).
assert (Hold : forall b m, In (b, m) (blocks Lc Ac) -> In (b, m) (b1 ++ b2)) by (intros b m Hb; rewrite <- Hblc; exact Hb).
assert (Hsep : forall b m, In (b, m) (blocks Lc Ac) -> r + NODE_SIZE <= b \/ b + m <= r).
{ intros b m Hb. pose proof (heap_sep _ _ LAWS Lm Am mem2 mdm b1 (r, NODE_SIZE) b2 (b, m) HH2 Hbl2 (Hold b m Hb)) as Hs. cbn [fst snd] in Hs. lia. }
assert (Hnp : r + NODE_SIZE <= palp \/ palp + zlen pal <= r).
{ destruct Hpalblk as (b & m & Hb & Hb1 & Hb2). destruct (Hsep b m Hb); lia. }
assert (Hnf : r + NODE_SIZE <= frp \/ frp + 4 * zlen fr <= r).
{ destruct Hfrblk as (b & m & Hb & Hb1 & Hb2). destruct (Hsep b m Hb); lia. }
assert (Hwb' : forall i, 0 <= i < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) (blocks Lm Am) (r + i)) by (intros i Hi; apply Hwb; [exact Hrin | exact Hi]).
assert (PRES : forall memx, journal ubs2_msyms MR STK sp0 FP L A mem md Lm Am memx mdm -> forall i, 0 <= i < NODE_SIZE -> present memx (r + i)).
{ intros memx HJx i Hi. exact (proj1 (heap_blocks _ _ LAWS Lm Am memx mdm r NODE_SIZE i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) Hrin Hi)). }
assert (WR : forall memx lo hi, journal ubs2_msyms MR STK sp0 FP L A mem md Lm Am memx mdm -> 0 <= lo -> hi <= NODE_SIZE ->
forall a, r + lo <= a < r + hi -> writable_at segs memx a).
{ intros memx lo hi HJx Hlo Hhi a Ha. replace a with (r + (a - r)) by lia. apply (present_writable ubs2_msyms). apply (PRES memx HJx). lia. }
assert (PALK : forall (m1 m2 : word -> option byte),
(forall a, 0 <= a < alloc_ceiling -> (r + NODE_SIZE <= a \/ a < r) ->
(exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) -> mbyte segs m2 a = mbyte segs m1 a) ->
arr8 segs m1 palp pal -> arr32 segs m1 frp fr -> arr8 segs m2 palp pal /\ arr32 segs m2 frp fr).
{ intros m1 m2 Hk Hp Hf. split.
- eapply arr8_frame; [exact Hp|]. intros a Ha. destruct Hpalblk as (b & m & Hb & Hb1 & Hb2).
pose proof (Hblk_rng b m Hb ltac:(lia)). apply Hk; [lia | lia | exists b, m; split; [exact Hb | lia]].
- eapply arr32_frame; [exact Hf|]. intros a Ha. destruct Hfrblk as (b & m & Hb & Hb1 & Hb2).
pose proof (Hblk_rng b m Hb ltac:(lia)). apply Hk; [lia | lia | exists b, m; split; [exact Hb | lia]]. }
destruct (PALK memc mem2 ltac:(intros a Ha Hr (b & m & Hb & Hab); replace a with (b + (a - b)) by lia; apply (Hkeep2 b m); [exact Hb | lia]) Hpa Hfa) as [Hpa2 Hfa2].
eapply SR_bind.
{ ltac2:(satvl ntn_p1 using (sat_vars ()) as LEM3); eapply (LEM3 fx regs2 mem2 HJ2 G2 G10 G18 G19 G20 G21 Hwb' (WR mem2 40 48 HJ2 ltac:(lia) ltac:(lia))). }
cbv beta. intros c2 (regs3 & mem3 & -> & HJ3 & G311 & G312 & G313 & G314 & Gk3 & Z3 & Vimin3 & Vimax3 & Hm3).
destruct (PALK mem2 mem3 ltac:(intros a Ha Hr _; apply Hm3; subst spc; lia) Hpa2 Hfa2) as [Hpa3 Hfa3].
assert (SV3 : saved_ok regs mem3) by (eapply saved_ok_frame; [exact SV2 | intros a Ha; apply Hm3; subst spc; lia]).
assert (HI1 : L1_inv API STK sp0 FP L A mem md Lm Am mdm regs palp frp imin imax r pal fr fx regs3 mem3 imin).
{ split; [exact HJ3|]. split; [exact Hfrm|].
split; [rewrite (Gk3 2%bv ltac:(cbv; tauto)); exact G2|]. split; [rewrite (Gk3 10%bv ltac:(cbv; tauto)); exact G10|].
split; [exact G311|]. split; [exact G313|]. split; [exact G312|]. split; [exact G314|]. split; [rewrite (Gk3 18%bv ltac:(cbv; tauto)); exact G18|].
split; [rewrite (Gk3 20%bv ltac:(cbv; tauto)); exact G20|]. split; [rewrite (Gk3 21%bv ltac:(cbv; tauto)); exact G21|].
split; [exact Hpa3|]. split; [exact Hfa3|].
exists 0, 0, 0, 0. rewrite !nlp_nil. cbn [wsum wdot fold_right].
repeat (split; [apply Z3; cbv; tauto|]). repeat (split; [lia|]). repeat split; apply is_intd_zero. }
eapply SR_bind.
{ ltac2:(satvl ntn_loop1 using (sat_vars ()) as LEM4); eapply (LEM4 (Z.to_nat (imax - imin)) fx regs3 mem3 imin ltac:(lia) ltac:(lia) HI1). }
cbv beta. intros c3 (fy1 & regs4 & mem4 & -> & HI1' & Gk4 & Hfp4 & Hm4).
destruct HI1' as (HJ4 & Hfrm4 & G42 & G410 & G411 & G413 & G412 & G414 & G418 & G420 & G421 & Hpa4 & Hfa4 & xs & xm0 & xm1 & xm2 &
V56 & V64 & V72 & V80 & V88 & V96 & Rs & R0 & R1 & R2 & Is & I0 & I1 & I2).
rewrite !nlp_full in Is, I0, I1, I2.
assert (SV4 : saved_ok regs mem4) by (eapply saved_ok_frame; [exact SV3 | intros a Ha; apply Hm4; subst spc; lia]).
eapply SR_bind.
{ ltac2:(satvl ntn_meandiv using (sat_vars ()) as LEM5); eapply (LEM5 fy1 regs4 mem4 xs xm0 xm1 xm2 HJ4 Hfrm4 G42 G410);
[ exact G421 | exact G418 | rewrite (Gk4 19%bv ltac:(cbv; tauto)), (Gk3 19%bv ltac:(cbv; tauto)); exact G19
| exact V56 | exact V64 | exact V72 | exact V80 | exact V88 | exact V96 | exact Rs | exact R0 | exact R1 | exact R2 | exact Is | exact I0 | exact I1 | exact I2
| exact Hwb' | exact (WR mem4 16 40 HJ4 ltac:(lia) ltac:(lia)) ]. }
cbv beta. intros c4 (fy2 & regs5 & mem5 & -> & HJ5 & Hfrm5 & G512 & G513 & G514 & Gk5 & Hfp5 &
(mn0 & mn1 & mn2 & M16 & M24 & M32 & Rm0 & Rm1 & Rm2 & Q0 & Q1 & Q2 & Le0 & Le1 & Le2) & Hm5).
destruct (PALK mem3 mem5 ltac:(intros a Ha Hr _; rewrite (Hm5 a) by lia; apply Hm4; subst spc; lia) Hpa3 Hfa3) as [Hpa5 Hfa5].
assert (SV5 : saved_ok regs mem5) by (eapply saved_ok_frame; [exact SV4 | intros a Ha; apply Hm5; subst spc; lia]).
assert (HI2 : L2_inv API STK sp0 FP L A mem md Lm Am mdm regs palp frp imin imax r pal fr mn0 mn1 mn2 fy2 regs5 mem5 imin).
{ split; [exact HJ5|]. split; [exact Hfrm5|].
split; [rewrite (Gk5 2%bv ltac:(cbv; tauto)); exact G42|]. split; [rewrite (Gk5 10%bv ltac:(cbv; tauto)); exact G410|].
split; [exact G512|]. split; [exact G513|]. split; [exact G514|]. split; [rewrite (Gk5 11%bv ltac:(cbv; tauto)); exact G411|].
split; [rewrite (Gk5 18%bv ltac:(cbv; tauto)); exact G418|].
split; [rewrite (Gk5 19%bv ltac:(cbv; tauto)), (Gk4 19%bv ltac:(cbv; tauto)), (Gk3 19%bv ltac:(cbv; tauto)); exact G19|].
split; [rewrite (Gk5 20%bv ltac:(cbv; tauto)); exact G420|]. split; [rewrite (Gk5 21%bv ltac:(cbv; tauto)); exact G421|].
split; [exact Hpa5|]. split; [exact Hfa5|]. split; [exact M16|]. split; [exact M24|]. split; [exact M32|].
exists 0, 0, 0, 0. rewrite !nlp_nil, Z.sub_diag. cbn [wsum fold_right neq_meanb existsb].
assert (Zk : forall o, In o [8; 16; 24; 32; 40; 48] -> val_mem segs mem5 (spc + o) 8 0).
{ intros o Ho. eapply val_mem_kept; [eapply val_mem_kept; [apply Z3; cbv [In] in Ho |- *; tauto|]|];
intros k Hk; cbv [In] in Ho; cbn in Hk; [apply Hm4 | apply Hm5]; subst spc; lia. }
repeat (split; [apply Zk; cbv; tauto|]). repeat (split; [lia|]). split; [apply is_intd_zero|].
repeat split; apply variance_init. }
eapply SR_bind.
{ ltac2:(satvl ntn_loop2 using (sat_vars ()) as LEM6); eapply (LEM6 (Z.to_nat (imax - imin)) fy2 regs5 mem5 imin ltac:(lia) ltac:(lia) HI2). }
cbv beta. intros c5 (fy3 & regs6 & mem6 & -> & HI2' & Gk6 & Hfp6 & Hm6).
destruct HI2' as (HJ6 & Hfrm6 & G62 & G610 & G612 & G613 & G614 & G611 & G618 & G619 & G620 & G621 & Hpa6 & Hfa6 & M16' & M24' & M32' & xs' & xv0 & xv1 & xv2 &
W8 & W16 & W24 & W32 & W40 & W48 & Rs' & Rv0 & Rv1 & Rv2 & Is' & Hv0 & Hv1 & Hv2).
rewrite !nlp_full in Is', Hv0, Hv1, Hv2.
assert (SV6 : saved_ok regs mem6) by (eapply saved_ok_frame; [exact SV5 | intros a Ha; apply Hm6; subst spc; lia]).
eapply SR_bind.
{ ltac2:(satvl ntn_va using (sat_vars ()) as LEM7); eapply (LEM7 fy3 regs6 mem6 xs' xv0 xv1 xv2 HJ6 Hfrm6 G62);
[ exact W8 | exact W16 | exact W24 | exact W32 | exact W40 | exact W48 | exact Rs' | exact Rv0 | exact Rv1 | exact Rv2 | exact Is' | exact Hv0 | exact Hv1 | exact Hv2 ]. }
cbv beta. intros c6 (fy4 & regs7 & mem7 & cut & -> & HJ7 & Hfrm7 & G715 & Hcut & Hsplit & Gk7 & Hm7).
assert (SV7 : saved_ok regs mem7) by (eapply saved_ok_frame; [exact SV6 | intros a Ha; apply Hm7; subst spc; lia]).
assert (Vn7 : val_mem segs mem7 nln 2 n0).
{ eapply val_mem_kept; [exact Hn0|]. intros k Hk. cbn in Hk.
rewrite (Hm7 k), (Hm6 k), (Hm5 k), (Hm4 k), (Hm3 k) by (subst spc; lia). apply K2n. lia. }
eapply SR_mono.
{ ltac2:(satvl ntn_tail using (sat_vars ()) as LEM8); eapply (LEM8 fy4 regs7 mem7 cut n0 HJ7);
[ rewrite (Gk7 2%bv ltac:(cbv; tauto)); exact G62
| rewrite (Gk7 8%bv ltac:(cbv; tauto)), (Gk6 8%bv ltac:(cbv; tauto)), (Gk5 8%bv ltac:(cbv; tauto)), (Gk4 8%bv ltac:(cbv; tauto)), (Gk3 8%bv ltac:(cbv; tauto)); exact G8
| rewrite (Gk7 9%bv ltac:(cbv; tauto)), (Gk6 9%bv ltac:(cbv; tauto)), (Gk5 9%bv ltac:(cbv; tauto)), (Gk4 9%bv ltac:(cbv; tauto)), (Gk3 9%bv ltac:(cbv; tauto)); exact G9
| rewrite (Gk7 10%bv ltac:(cbv; tauto)); exact G610
| exact G715 | exact Hcut | exact SV7 | exact Vn7 | exact Rn0 | exact Hwb' | exact (WR mem7 48 51 HJ7 ltac:(lia) ltac:(lia)) ]. }
cbv beta. intros c7 (regs8 & mem8 & -> & HJ8 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T10 & Gk8 & Vcut & Vcidx & Vleaf & Vn1 & Hm8).
exists fy4, Lm, Am, regs8, mem8, mdm, r.
split; [reflexivity|]. split; [exact Hfrm7|]. split; [exact HJ8|]. split; [exact Hid2|].
split.
{ apply regs_preserved_of_list. intros rr Hrr. cbv [CALLEE_SAVED In] in Hrr.
repeat (destruct Hrr as [<-|Hrr];
[first [assumption
| lazymatch goal with |- getr _ ?k = _ =>
rewrite (Gk8 k ltac:(cbv; tauto)), (Gk7 k ltac:(cbv; tauto)), (Gk6 k ltac:(cbv; tauto)), (Gk5 k ltac:(cbv; tauto)),
(Gk4 k ltac:(cbv; tauto)), (Gk3 k ltac:(cbv; tauto)); apply (Gk2 k); cbv; tauto end] |]). destruct Hrr. }
split; [exact T10|].
assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - NTN_STK <= a < spZ regs) -> ~ (nln <= a < nln + 2) -> mbyte segs mem8 a = mbyte segs memc a).
{ intros a Ha Hna Hnn. rewrite (Hm8 a), (Hm7 a), (Hm6 a), (Hm5 a), (Hm4 a), (Hm3 a) by (subst spc; lia). apply Hhi2; [exact Ha | subst spc; lia]. }
split; [exact KHI|].
assert (KBL : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte segs mem8 (b + i) = mbyte segs memc (b + i)).
{ intros b m i Hb Hi. pose proof (Hblk_rng b m Hb ltac:(lia)) as [Hb0 Hb1]. pose proof (Hsep b m Hb) as Hs.
rewrite (Hm8 (b + i)), (Hm7 (b + i)), (Hm6 (b + i)), (Hm5 (b + i)), (Hm4 (b + i)), (Hm3 (b + i)) by (subst spc; lia).
apply (Hkeep2 b m); [exact Hb | exact Hi]. }
split; [exact KBL|].
right. split; [exact Hrnz|]. split; [exact Hr16|]. split; [exists b1, b2; split; [exact Hbl2 | exact Hblc]|]. split; [exact Hwb|].
split; [exact Vn1|].
assert (Vimin8 : val_mem segs mem8 (r + 40) 4 imin).
{ eapply val_mem_kept; [exact Vimin3|]. intros k Hk. cbn in Hk. rewrite (Hm8 k), (Hm7 k), (Hm6 k), (Hm5 k), (Hm4 k) by (subst spc; lia). reflexivity. }
assert (Vimax8 : val_mem segs mem8 (r + 44) 4 imax).
{ eapply val_mem_kept; [exact Vimax3|]. intros k Hk. cbn in Hk. rewrite (Hm8 k), (Hm7 k), (Hm6 k), (Hm5 k), (Hm4 k) by (subst spc; lia). reflexivity. }
assert (MK : forall off v, 16 <= off -> off + 8 <= 40 -> val_mem segs mem5 (r + off) 8 v -> val_mem segs mem8 (r + off) 8 v).
{ intros off v Ho1 Ho2 Hv. eapply val_mem_kept; [exact Hv|]. intros k Hk. cbn in Hk. rewrite (Hm8 k), (Hm7 k), (Hm6 k) by (subst spc; lia). reflexivity. }
destruct (val_mem_of_present8 segs mem8 r ltac:(intros i Hi; apply mbyte_of_present; apply (PRES mem8 HJ8); lia)) as (c0 & Rc0 & Vc0).
destruct (val_mem_of_present8 segs mem8 (r + 8) ltac:(intros i Hi; rewrite <- Z.add_assoc; apply mbyte_of_present; apply (PRES mem8 HJ8); lia)) as (c1 & Rc1 & Vc1).
exists (mkTN r [mn0; mn1; mn2] imin imax cut cidx). cbn [tn_addr tn_imin tn_imax tn_cidx tn_cut tn_mean].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ cbn [tree_at tn_addr tn_mean]. split; [exact Hrnz|]. split; [reflexivity|]. exists c0, c1.
cbn [obj_at LAY_Node node_vals tn_mean tn_imin tn_imax tn_cut tn_cidx app]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N Z.mul Pos.mul].
rewrite Z.add_0_r.
split; [split; [exact Vc0 | exact Rc0]|]. split; [split; [exact Vc1 | exact Rc1]|].
split; [split; [apply MK; [lia | lia | exact M16] | exact Rm0]|]. split; [split; [apply MK; [lia | lia | exact M24] | exact Rm1]|].
split; [split; [apply MK; [lia | lia | exact M32] | exact Rm2]|].
split; [split; [exact Vimin8 | lia]|]. split; [split; [exact Vimax8 | lia]|].
split; [split; [exact Vcut | lia]|]. split; [split; [exact Vcidx | lia]|]. split; [split; [exact Vleaf | lia]|]. exact I. }
split.
{ unfold tnode_wf. cbn [tn_cut tn_cidx tn_imin tn_imax tn_mean]. repeat (split; [lia|]). split; [reflexivity|].
repeat constructor; lia. }
split.
{ intros d Hd. assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by lia.
destruct Hd3 as [-> | [-> | ->]]; cbn [Z.to_nat nth Pos.to_nat Pos.iter_op]; [exact Q0 | exact Q1 | exact Q2]. }
exact Hsplit.
Qed.
End S.
End c.
