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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC9a AC9d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92 AC9h.
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
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Local Ltac sep HSEP i j := septac HSEP i j; lia.
Lemma tinit_segX : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs6 : bvmap 5 word) mem6 md6 (regs0 : bvmap 5 word) (PIX : list Z),
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem6 md6 7 ->
z_gp cx = as_gp B -> z_tp cx = as_tp B ->
init_regs regs6 cx -> init_mem (mrestrict (w_H W7) mem6) cx -> tlzw_frame (mrestrict (w_H W7) mem6) (z_sp cx) regs0 ->
garr8 SEGS (mrestrict (w_H W7) mem6) (z_img cx) PIX -> length PIX = Z.to_nat (z_nP cx) ->
SRr SEGS W7 (mkCfg (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) mem6 (seg_rom SEGS)) md6)
(fun W' c' => W' = W7 /\ exists regsH memH mdH TM0,
c' = mkCfg (mkst regsH (Z_to_bv 64 (BASE + PC_HEAD)) memH (seg_rom SEGS)) mdH /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memH mdH 7 /\
alzw_regs_head regsH cx /\ getr regsH 23 = w64 0 /\
agen_at (mrestrict (w_H W7) memH) cx 1 (z_idl cx + 2) 1 /\
atables_at (mrestrict (w_H W7) memH) cx (lzw_init (z_idl cx) TM0) /\ lzw_inv (z_idl cx) (z_nP cx) (lzw_init (z_idl cx) TM0) /\
alzw_slots (mrestrict (w_H W7) memH) cx /\ alzw_sslots (mrestrict (w_H W7) memH) cx /\ tlzw_frame (mrestrict (w_H W7) memH) (z_sp cx) regs0 /\
(forall a, 0 <= a < 2 ^ 64 -> init_untouched cx a -> mbyte SEGS (mrestrict (w_H W7) memH) a = mbyte SEGS (mrestrict (w_H W7) mem6) a) /\
vtabs_at SEGS (mrestrict (w_H W7) memH) cx PIX (mkLV (repeat 0 4096) [z_idl cx]) /\
vinv cx PIX (lzw_init (z_idl cx) TM0) (mkLV (repeat 0 4096) [z_idl cx])).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs6 mem6 md6 regs0 PIX HCX HRG HSEP HBL HTOK HJ Hzgp Hztp HIR HIM HFR GPIX LenPIX.
destruct (tinit_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs6 mem6 md6 regs0 HCX HRG HSEP HBL HTOK HJ HIR HIM HFR)
as (E & TM0 & HEI & HS & HEnv & LenTM & ATM).
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
assert (HK : forall a, 0 <= a < 2 ^ 64 -> init_untouched cx a -> mbyte SEGS (mrestrict (w_H W7) mem6) a = mbyte SEGS (mrestrict (w_H W7) mem6) a) by (intros; reflexivity).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) mem6 (seg_rom SEGS)))).
change mem6 with (ms_mem (mkst regs6 (Z_to_bv 64 (BASE + PC_INIT)) mem6 (seg_rom SEGS))) in HJ.
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
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte SEGS mo a = mbyte SEGS ?mz a |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte SEGS mn a = mbyte SEGS mz a)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5 R6 R7; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte SEGS mo a = Some ?v |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte SEGS mn a = Some v)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5 R6 R7; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
end
end; clear T.
Local Ltac awr3 cx AG HE8 HE2 HE10 Actx HBg Ald HBld :=
cbn [ss_mem ss_init]; unfold ictx_region, istk_region, ild_region;
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (z_ctx cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (z_ctx cx + (a - z_ctx cx)) by lia; apply Actx; [exact HBg | lia]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 2%nat) by lia; rewrite HE2, unsigned_lit_small by lia; lia
| cbn; lia | cbn; lia
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat (z_ld cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 10%nat) by lia; rewrite HE10; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (z_ld cx + (a - z_ld cx)) by lia; apply Ald; [exact HBld | lia]
| apply awr_ok_nil ] ] ].
Local Ltac tstep cx AG HE8 HE2 HE10 HSEP R1 R2 R3 R4 R5 R6 R7 :=
let T := fresh "T" in
lazymatch goal with HFr : frame_of ?Ef _ (mrestrict ?Hh ?ma) (mrestrict _ ?mb) |- _ =>
cbn [ss_mem ss_init] in HFr;
assert (T : forall a, 0 <= a < 2 ^ 64 ->
(~ (z_ctx cx + 60 <= a < z_ctx cx + 68) /\ ~ (z_sp cx - 320 + 24 <= a < z_sp cx - 320 + 112) /\ ~ (z_ld cx <= a < z_ld cx + 2)) ->
mbyte SEGS (mrestrict Hh mb) a = mbyte SEGS (mrestrict Hh ma) a)
by (intros a Ha Hu;
eapply (aframe_mbyte_list Ef _ _ _ [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 24, z_sp cx - 320 + 112); (z_ld cx, z_ld cx + 2)] a HFr Ha);
[ repeat (apply Forall2_cons;
[ right; cbn [fst snd YP09.r_base YP09.r_wlo YP09.r_whi ss_mem ss_init ictx_region istk_region ild_region base_val ew ewset Nat.eqb];
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
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
pmkst HS; ppcs;
idtac;
let L := getLAWS in let HSGL := aj_segs_low in
eapply SRr_bind;
[ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at SEGS B L HSGL OSet (SIGMA AS_asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX) _ _ _ _ _ _ _ _ _ _ _ _ 7
dval 0 nval (-320) (Z_to_bv 64 raval) HJ) end;
[ rewrite Ra0; eatom AG HEd
| rewrite Ra1; reflexivity
| rewrite Ra2; first [reflexivity | match goal with H : ew _ 39 = _ |- _ => eatom AG H end]
| lia | lia | lia
| unfold spZ; rewrite Rsp; try rewrite (AG 2%nat) by lia; rewrite HE2, unsigned_lit_small by lia; lia
| reflexivity | lia | unfold ESTACK; lia
| rewrite Rgp; try rewrite (AG 3%nat) by lia; rewrite HE3, Hzgp; reflexivity
| rewrite Rtp; try rewrite (AG 4%nat) by lia; rewrite HE4, Hztp; reflexivity
| exact Rra | apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]
| intros a Ha; split; [replace a with (dval + (a - dval)) by lia; apply Atmp; [exact HB | lia] | unfold ESTACK; lia]
| eapply (amem_range_of_block SEGS B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| eapply (range_addressable_of_block SEGS B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| intros _; eapply (shadow_hull_vis_of_block SEGS B L _ _ _ _ _ _ _ _ _ (proj1 HJ) HB); lia
| exact I ]
| cbv beta; clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp ].
Local Ltac mpost cx Heff Hfr dval nval Zname HSEP R1 R2 R3 R4 R5 R6 R7 :=
let T := fresh "T" in
lazymatch type of Hfr with forall a, _ -> _ -> _ -> aview _ (w_H ?Wx) ?m2 a = aview _ _ ?m1 a =>
assert (Zname : forall a, 0 <= a < 2 ^ 64 -> in_rng dval (dval + nval) a -> mbyte SEGS (mrestrict (w_H Wx) m2) a = Some (Z_to_bv 8 0))
by (intros a Ha Hd; unfold in_rng in Hd; replace a with (dval + (a - dval)) by lia; apply mbyte_zero_of_aview; rewrite (Heff (a - dval)) by lia; reflexivity);
assert (T : forall a, 0 <= a < 2 ^ 64 -> (~ (dval <= a < dval + nval) /\ ~ (z_sp cx - 320 - 4096 <= a < z_sp cx - 320)) ->
mbyte SEGS (mrestrict (w_H Wx) m2) a = mbyte SEGS (mrestrict (w_H Wx) m1) a)
by (intros a Ha [Hn1 Hn2]; apply (mbyte_of_aview SEGS); apply Hfr; [exact Ha | exact Hn1 | unfold ESTACK; replace (z_sp cx + -320) with (z_sp cx - 320) by lia; exact Hn2]);
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
paj_run_tok RUN HS HJ SHOK Bspan; try (oblk HJ HBld HE10 HE27 (z_ld cx)); try (oblk HJ HBg HE8 HE27 (z_ctx cx)).
{ awr3 cx AG HE8 HE2 HE10 Actx HBg Ald HBld. }
tstep cx AG HE8 HE2 HE10 HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
mcall cx HS HJ AG HE54 HE2 HE3 HE4 Hzgp Hztp (z_ti cx) (2 * z_idl cx * z_idl cx) (BASE + 0x16ec) HBti Ati.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff1 & Hfr1 & Hpres2).
reseat HS HJ2 HP2 [0; 1; 2]%nat AG ltac:(kept3 AG HE8 HE2 HE10 Hfr1 Hpres2 HSEP 1%nat).
mpost cx Heff1 Hfr1 (z_ti cx) (2 * z_idl cx * z_idl cx) ZTI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 0x16ec)) mem2 (seg_rom SEGS))) in HJ2. reshok_bx HS 27%nat.
Local Ltac stretch cx HS HJ SHOK AG HE8 HE2 HE10 Actx HBg Ald HBld HSEP R1 R2 R3 R4 R5 R6 R7 :=
let HEv8 := fresh "HEv8" in let HEv27 := fresh "HEv27" in
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (try rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv27 : ew Ev 27 = Z_to_bv 64 SB) by (try rewrite (AG 27%nat) by lia; match goal with H27 : ew _ 27 = Z_to_bv 64 SB |- _ => exact H27 end) end;
paj_run_tok RUN HS HJ SHOK Bspan; try (oblk HJ HBg HEv8 HEv27 (z_ctx cx)); clear HEv8 HEv27;
[ awr3 cx AG HE8 HE2 HE10 Actx HBg Ald HBld | ];
[ tstep cx AG HE8 HE2 HE10 HSEP R1 R2 R3 R4 R5 R6 R7 ].
stretch cx HS HJ2 SHOK AG HE8 HE2 HE10 Actx HBg Ald HBld HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
mcall cx HS HJ2 AG HE55 HE2 HE3 HE4 Hzgp Hztp (z_lm cx) 8192 (BASE + 0x1704) HBlm Alm.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff2 & Hfr2 & Hpres3).
reseat HS HJ3 HP3 [0; 1; 2]%nat AG ltac:(kept3 AG HE8 HE2 HE10 Hfr2 Hpres3 HSEP 2%nat).
mpost cx Heff2 Hfr2 (z_lm cx) 8192 ZLM HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (BASE + 0x1704)) mem3 (seg_rom SEGS))) in HJ3. reshok_bx HS 27%nat.
stretch cx HS HJ3 SHOK AG HE8 HE2 HE10 Actx HBg Ald HBld HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
mcall cx HS HJ3 AG HE37 HE2 HE3 HE4 Hzgp Hztp (z_lc cx) 4096 (BASE + 0x1720) HBlc Alc.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff3 & Hfr3 & Hpres4).
reseat HS HJ4 HP4 [0; 1; 2]%nat AG ltac:(kept3 AG HE8 HE2 HE10 Hfr3 Hpres4 HSEP 3%nat).
mpost cx Heff3 Hfr3 (z_lc cx) 4096 ZLC HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 (BASE + 0x1720)) mem4 (seg_rom SEGS))) in HJ4. reshok_bx HS 27%nat.
stretch cx HS HJ4 SHOK AG HE8 HE2 HE10 Actx HBg Ald HBld HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
mcall cx HS HJ4 AG HE56 HE2 HE3 HE4 Hzgp Hztp (z_li cx) 8192 (BASE + 0x173c) HBli Ali.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff4 & Hfr4 & Hpres5).
reseat HS HJ5 HP5 [0; 1; 2]%nat AG ltac:(kept3 AG HE8 HE2 HE10 Hfr4 Hpres5 HSEP 4%nat).
mpost cx Heff4 Hfr4 (z_li cx) 8192 ZLI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo HnP HMR0.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 (BASE + 0x173c)) mem5 (seg_rom SEGS))) in HJ5. reshok_bx HS 27%nat.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEw8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEw27 : ew Ev 27 = Z_to_bv 64 SB) by (rewrite (AG 27%nat) by lia; exact HE27) end.
paj_run_to_tok RUNTO HS HJ5 SHOK Bspan PC_HEAD; try (oblk HJ5 HBg HEw8 HEw27 (z_ctx cx)); [ awr3 cx AG HE8 HE2 HE10 Actx HBg Ald HBld | ].
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
assert (G8 : bv_unsigned (ew Ev 8) = z_ctx cx) by (rewrite HEv8; apply unsigned_lit_small; lia);
assert (G10 : bv_unsigned (ew Ev 10) = z_ld cx) by (rewrite HEv10; apply unsigned_lit_small; lia)
end.
clear HE2 HE3 HE4 HE8 HE10 HE27 HE21 HE25 HE32.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (st_ok_pi_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HRg0; pose proof (st_ok_pi_region_nth Ex ssx msx 1%nat _ HS eq_refl) as HRg1;
pose proof (st_ok_pi_region_nth Ex ssx msx 2%nat _ HS eq_refl) as HRg2 end.
cbn [ms_mem restrict] in HRg0, HRg1, HRg2.
Local Ltac aregE HS AG :=
lazymatch goal with |- context [getr _ ?r] =>
let R := fresh "R" in prreg HS r R; rewrite R; clear R;
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
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc].
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
split; [| split; [exact HK|] ].
{ eapply tlzw_frame_agree; [exact HFR|]. intros a Ha. apply HK; [lia|]. unfold init_untouched. repeat split; lia. }
lazymatch goal with |- vtabs_at _ ?mx _ _ _ /\ _ =>
assert (Vld0 : val_mem SEGS mx (z_ld cx + 0) 2 (z_idl cx)) by (fld HRg2 G10)
end.
rewrite Z.add_0_r in Vld0.
split; [| split; [cbn [v_LC]; apply repeat_length | split; [exact LenPIX | cbn [v_LD length la_lp lzw_init]; lia]]].
subst m.
eapply (vtabs_init SEGS (mrestrict (w_H W7) mem6) _ cx PIX (fun a => ~ init_untouched cx a) (z_idl cx) GPIX LenPIX ltac:(lia)).
- intros a Ha Hna. apply HK; [exact Ha|]. unfold init_untouched in Hna |- *. tauto.
- intros a Ha. split; [lia|]. intros Hn; apply Hn. unfold init_untouched.
septac HSEP 6%nat 7%nat. septac HSEP 0%nat 7%nat. septac HSEP 1%nat 7%nat. septac HSEP 2%nat 7%nat. septac HSEP 3%nat 7%nat. septac HSEP 4%nat 7%nat.
repeat split; lia.
- intros a Ha. apply ZLC; [lia | unfold in_rng; lia].
- exact Vld0.
- lia.
Qed.
End S.
End d.
End b.
