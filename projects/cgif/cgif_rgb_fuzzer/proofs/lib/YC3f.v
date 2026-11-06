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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC0x YC3g YC2z YC3e YC31 YC2x YC2v YC35 YC2y YC2w YC37 YC3a YC3b YC3c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition rst_pc (full1 : bool) : Z := if full1 then PC_RST1 else PC_RST2.
Definition rst_rlp (full1 : bool) : bv 5 := if full1 then 13%bv else 16%bv.
Definition rst_rti (full1 : bool) : bv 5 := if full1 then 7%bv else 15%bv.
Definition ss_trst (full1 : bool) : sstate :=
alzw_ss (rst_pc full1) (sr_set (sr_set asr_t5 (rst_rlp full1) (SOff 33 (-1))) (rst_rti full1) (SOff 53 0)) true false []
[ (23%nat, mkAF 0 99999999 0) ] [ mkAC BC_LTU (SOff 23 0) (SOff 59 0) ] [].
Definition rst_untouched (cx : lzw_acx) (a : Z) : Prop :=
~ (z_ctx cx + 60 <= a < z_ctx cx + 68) /\ ~ (z_ti cx <= a < z_ti cx + 2 * z_idl cx * z_idl cx) /\
~ (z_lm cx <= a < z_lm cx + 8192) /\ ~ (z_lc cx <= a < z_lc cx + 4096) /\ ~ (z_li cx <= a < z_li cx + 8192) /\
~ (z_sp cx - 320 - 4096 <= a < z_sp cx - 320).
Definition in_rng (lo hi a : Z) : Prop := lo <= a < hi.
Lemma arr16_zeros_aview : forall H (mem : word -> option byte) base n,
(forall a, base <= a < base + 2 * Z.of_nat n -> mbyte trasegs (mrestrict H mem) a = Some (Z_to_bv 8 0)) ->
arr16 trasegs (mrestrict H mem) base (repeat 0 n).
Proof. intros H mem base n Hz. apply arr16_zeros. exact Hz. Qed.
Section S.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Let HBcode := tl_code B TL.
Local Ltac sep HSEP i j := septac HSEP i j; lia.
Local Ltac zsep HSEP C :=
lazymatch C with
| rst_untouched _ => unfold rst_untouched in *; tauto
| in_rng (z_ti _) _ => unfold in_rng in *; septac HSEP 1%nat 6%nat; septac HSEP 1%nat 2%nat; septac HSEP 1%nat 3%nat; septac HSEP 1%nat 4%nat; lia
| in_rng (z_lm _) _ => unfold in_rng in *; septac HSEP 2%nat 6%nat; septac HSEP 1%nat 2%nat; septac HSEP 2%nat 3%nat; septac HSEP 2%nat 4%nat; lia
| in_rng (z_lc _) _ => unfold in_rng in *; septac HSEP 3%nat 6%nat; septac HSEP 1%nat 3%nat; septac HSEP 2%nat 3%nat; septac HSEP 3%nat 4%nat; lia
| in_rng (z_li _) _ => unfold in_rng in *; septac HSEP 4%nat 6%nat; septac HSEP 1%nat 4%nat; septac HSEP 2%nat 4%nat; septac HSEP 3%nat 4%nat; lia
end.
Local Ltac fold_step T HSEP R1 R2 R3 R4 R5 :=
lazymatch type of T with forall a, _ -> _ -> mbyte _ ?mn a = mbyte _ ?mo a =>
repeat match goal with
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte trasegs mo a = mbyte trasegs ?mz a |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte trasegs mn a = mbyte trasegs mz a)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
| H : forall a, 0 <= a < 2 ^ 64 -> ?C a -> mbyte trasegs mo a = Some ?v |- _ =>
let H2 := fresh H in
assert (H2 : forall a, 0 <= a < 2 ^ 64 -> C a -> mbyte trasegs mn a = Some v)
by (intros a Ha Hc; rewrite (T a Ha) by (clear - Ha Hc HSEP R1 R2 R3 R4 R5; zsep HSEP C); exact (H a Ha Hc));
clear H; rename H2 into H
end
end; clear T.
Local Ltac stretch cx HS HJ SHOK AG HE8 Actx HBg HSEP R1 R2 R3 R4 R5 :=
let HEv8 := fresh "HEv8" in let HEv27 := fresh "HEv27" in
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (try rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv27 : ew Ev 27 = Z_to_bv 64 SB) by (try rewrite (AG 27%nat) by lia; match goal with H27 : ew _ 27 = Z_to_bv 64 SB |- _ => exact H27 end) end;
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; try (oblk HJ HBg HEv8 HEv27 (z_ctx cx)); clear HEv8 HEv27;
[ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (z_ctx cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi actx_region]; intros a Ha; replace a with (z_ctx cx + (a - z_ctx cx)) by lia; apply Actx; [exact HBg | lia]
| apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ]
| ];
[ let T := fresh "T" in
lazymatch goal with HFr : frame_of ?Ef _ (mrestrict ?Hh ?ma) (mrestrict _ ?mb) |- _ =>
assert (T : forall a, 0 <= a < 2 ^ 64 -> ~ (z_ctx cx + 60 <= a < z_ctx cx + 68) -> mbyte trasegs (mrestrict Hh mb) a = mbyte trasegs (mrestrict Hh ma) a)
by (intros a Ha Hu;
eapply (aframe_mbyte_list Ef _ _ _ [(z_ctx cx + 60, z_ctx cx + 68); (0, 0)] a HFr Ha);
[ apply Forall2_cons; [right; cbn [fst snd YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi actx_region base_val ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8, unsigned_lit_small by lia; lia |];
apply Forall2_cons; [left; cbn; lia | apply Forall2_nil]
| cbn; split; [exact Hu | split; [lia | exact I]] ]);
clear HFr; try match goal with H : frame_of _ _ _ _ |- _ => clear H end; try match goal with H : mem_grows _ _ |- _ => clear H end;
fold_step T HSEP R1 R2 R3 R4 R5
end ].
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
| rewrite Ra2; first [reflexivity | match goal with H : ew _ 38 = _ |- _ => eatom AG H end]
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
Local Ltac mpost cx Heff Hfr dval nval Zname HSEP R1 R2 R3 R4 R5 :=
let T := fresh "T" in
lazymatch type of Hfr with forall a, _ -> _ -> _ -> aview _ (w_H ?Wx) ?m2 a = aview _ _ ?m1 a =>
assert (Zname : forall a, 0 <= a < 2 ^ 64 -> in_rng dval (dval + nval) a -> mbyte trasegs (mrestrict (w_H Wx) m2) a = Some (Z_to_bv 8 0))
by (intros a Ha Hd; unfold in_rng in Hd; replace a with (dval + (a - dval)) by lia; apply mbyte_zero_of_aview; rewrite (Heff (a - dval)) by lia; reflexivity);
assert (T : forall a, 0 <= a < 2 ^ 64 -> (~ (dval <= a < dval + nval) /\ ~ (z_sp cx - 320 - 4096 <= a < z_sp cx - 320)) ->
mbyte trasegs (mrestrict (w_H Wx) m2) a = mbyte trasegs (mrestrict (w_H Wx) m1) a)
by (intros a Ha [Hn1 Hn2]; apply (mbyte_of_aview trasegs); apply Hfr; [exact Ha | exact Hn1 | unfold ESTACK; replace (z_sp cx + -320) with (z_sp cx - 320) by lia; exact Hn2]);
clear Heff Hfr; fold_step T HSEP R1 R2 R3 R4 R5
end.
Lemma trst_seg : forall (full1 : bool) cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s',
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
arst_pre full1 cx X s' regs (mrestrict (w_H W7) memT) -> z_gp cx = as_gp B -> z_tp cx = as_tp B ->
SRr trasegs W7 (mkCfg (mkst regs (Z_to_bv 64 (rst_pc full1)) memT (seg_rom trasegs)) mdT)
(tmiss_tail_post B cx lyc Sc W memc mdc ly7 S7 W7 memT X s').
Proof.
intros full1 cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s' HCX HRG HSEP (HBg & HBi & HBt) HTOK HJ HSL HSS HFR
(HFX & H30 & H12 & H7 & HG & HT & HI & Hdp & H24 & Hs') Hzgp Hztp.
fold (rst_rlp full1) in H12. fold (rst_rti full1) in H7.
pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
miss_prep B cx HCX HRG HBt HTOK HJ.
assert (Ati : forall blc lyq i, In (z_ti cx, 2 * z_idl cx * z_idl cx) blc -> 0 <= i < req_size (2 * z_idl cx * z_idl cx) ->
awr_byte (336 + 16384) (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ti cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_ti cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; right; left; reflexivity)); [exact Hb | exact Hi]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
destruct HT as (ATI & ALM & ALI & ATM).
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; split; [nia|nia]).
unfold z_tisz, z_tmsz in *.
set (m := mrestrict (w_H W7) memT) in *.
remember (Ereg regs (acx_extra cx (lp + 1) (z_idl cx + 2) 1 regs0 ++ [])) as E eqn:HE0.
pose proof (AE_sp regs cx (lp + 1) (z_idl cx + 2) 1 regs0 [] HFC) as HE2. pose proof (AE_ctx regs cx (lp + 1) (z_idl cx + 2) 1 regs0 [] HFC) as HE8.
pose proof (AE_SB regs cx (lp + 1) (z_idl cx + 2) 1 regs0 [] HFC) as HE27. pose proof (AE_idl regs cx (lp + 1) (z_idl cx + 2) 1 regs0 [] HFC) as HE25.
pose proof (AE_ti regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE53. pose proof (AE_lm regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE54.
pose proof (AE_li regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE56. pose proof (AE_lc regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE55.
pose proof (AE_tm regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE57. pose proof (AE_nP regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE59.
pose proof (AE_ld regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE58. pose proof (AE_img regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE32.
pose proof (AE_lp regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE33. pose proof (AE_dp regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE34.
pose proof (AE_mp regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE35. pose proof (AE_tisz regs cx (lp + 1) (z_idl cx + 2) 1 regs0 []) as HE38.
pose proof (AE_gp regs cx (lp + 1) (z_idl cx + 2) 1 regs0 [] HFC) as HE3. pose proof (AE_tp regs cx (lp + 1) (z_idl cx + 2) 1 regs0 [] HFC) as HE4.
rewrite <- HE0 in HE2, HE8, HE27, HE25, HE53, HE54, HE56, HE55, HE57, HE59, HE58, HE32, HE33, HE34, HE35, HE38, HE3, HE4.
unfold z_tisz in HE38.
assert (HE23 : ew E 23 = Z_to_bv 64 s') by (rewrite HE0, (AE_reg regs _ _ _ _ _ [] 23%bv 23) by reflexivity; exact H24).
assert (HS1 : st_ok trasegs E (alzw_ss (rst_pc full1) asr_t5 true false [] [ (23%nat, mkAF 0 99999999 0) ] [ mkAC BC_LTU (SOff 23 0) (SOff 59 0) ] [])
(mkst regs (Z_to_bv 64 (rst_pc full1)) m (seg_rom trasegs))).
{ rewrite HE0. apply (alzw_st_ok cx regs regs0 (lp + 1) (z_idl cx + 2) 1 [] m (rst_pc full1) asr_t5 true false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros _ a Ha. apply (apresent_writable trasegs). apply (proj1 (Hcpres a ltac:(lia))).
- intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_t5 regs cx); [exact HFX | exact H30 | lia | lia].
- vm_compute; reflexivity.
- apply Forall_nil.
- exact I. - exact I. - exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE23, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
- cbn [conds_ok]. split; [apply (cond_ltu E 23 0 59 0 s' (z_nP cx) HE23 HE59); lia | exact I].
- exact I. }
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (rst_pc full1)) m (seg_rom trasegs)) (rst_rlp full1) (SOff 33 (-1)) HS1 ltac:(destruct full1; reflexivity)
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE33, unsigned_lit_small by lia; rewrite H12; unfold w64; f_equal; lia)) as HS1b.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (rst_pc full1)) m (seg_rom trasegs)) (rst_rti full1) (SOff 53 0) HS1b ltac:(destruct full1; reflexivity)
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE53, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H7)) as HS.
clear HS1b.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts alzw_ss] in HS.
subst m. rewrite <- restrict_mkst_fx in HS.
set (m := mrestrict (w_H W7) memT) in *.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> rst_untouched cx a -> mbyte trasegs (mrestrict (w_H W7) memT) a = mbyte trasegs (mrestrict (w_H W7) memT) a) by (intros; reflexivity).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
destruct full1; cbn [rst_pc rst_rlp rst_rti] in HS |- *.
-
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_RST1) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_RST1) memT (seg_rom trasegs))) in HJ.
stretch cx HS HJ SHOK AG HE8 Actx HBg HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
mcall cx HS HJ AG HE53 HE2 HE3 HE4 Hzgp Hztp (z_ti cx) (2 * z_idl cx * z_idl cx) 0x89f3c HBti Ati.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff1 & Hfr1 & Hpres2).
reseat HS HJ2 HP2 [0; 1]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [try rewrite (AG 8%nat) by lia; rewrite HE8 | try rewrite (AG 2%nat) by lia; rewrite HE2];
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr1; [lia | revert Ha; first [sep HSEP 1%nat 6%nat | lia] | unfold ESTACK; lia]
| exact Hpres2 ]).
mpost cx Heff1 Hfr1 (z_ti cx) (2 * z_idl cx * z_idl cx) ZTI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 0x89f3c) mem2 (seg_rom trasegs))) in HJ2. reshok_bx HS 27%nat.
stretch cx HS HJ2 SHOK AG HE8 Actx HBg HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
mcall cx HS HJ2 AG HE54 HE2 HE3 HE4 Hzgp Hztp (z_lm cx) 8192 0x89f54 HBlm Alm.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff2 & Hfr2 & Hpres3).
reseat HS HJ3 HP3 [0; 1]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [rewrite (AG 8%nat) by lia; rewrite HE8 | rewrite (AG 2%nat) by lia; rewrite HE2];
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr2; [lia | revert Ha; first [sep HSEP 2%nat 6%nat | lia] | unfold ESTACK; lia]
| exact Hpres3 ]).
mpost cx Heff2 Hfr2 (z_lm cx) 8192 ZLM HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 0x89f54) mem3 (seg_rom trasegs))) in HJ3. reshok_bx HS 27%nat.
stretch cx HS HJ3 SHOK AG HE8 Actx HBg HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
mcall cx HS HJ3 AG HE55 HE2 HE3 HE4 Hzgp Hztp (z_lc cx) 4096 0x89f70 HBlc Alc.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff3 & Hfr3 & Hpres4).
reseat HS HJ4 HP4 [0; 1]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [rewrite (AG 8%nat) by lia; rewrite HE8 | rewrite (AG 2%nat) by lia; rewrite HE2];
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr3; [lia | revert Ha; first [sep HSEP 3%nat 6%nat | lia] | unfold ESTACK; lia]
| exact Hpres4 ]).
mpost cx Heff3 Hfr3 (z_lc cx) 4096 ZLC HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 0x89f70) mem4 (seg_rom trasegs))) in HJ4. reshok_bx HS 27%nat.
stretch cx HS HJ4 SHOK AG HE8 Actx HBg HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
mcall cx HS HJ4 AG HE56 HE2 HE3 HE4 Hzgp Hztp (z_li cx) 8192 0x8a04c HBli Ali.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff4 & Hfr4 & Hpres5).
reseat HS HJ5 HP5 [0; 1]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [rewrite (AG 8%nat) by lia; rewrite HE8 | rewrite (AG 2%nat) by lia; rewrite HE2];
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr4; [lia | revert Ha; first [sep HSEP 4%nat 6%nat | lia] | unfold ESTACK; lia]
| exact Hpres5 ]).
mpost cx Heff4 Hfr4 (z_li cx) 8192 ZLI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 0x8a04c) mem5 (seg_rom trasegs))) in HJ5. reshok_bx HS 27%nat.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEw8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEw27 : ew Ev 27 = Z_to_bv 64 SB) by (rewrite (AG 27%nat) by lia; exact HE27) end.
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK Bspan PC_HEAD; try (oblk HJ5 HBg HEw8 HEw27 (z_ctx cx)).
clear HEw8 HEw27.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (z_ctx cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi actx_region]; intros a Ha; replace a with (z_ctx cx + (a - z_ctx cx)) by lia; apply Actx; [exact HBg | lia]
| apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ]. }
lazymatch goal with HFr : frame_of ?Ef _ (mrestrict ?Hh ?ma) (mrestrict _ ?mb) |- _ =>
assert (T5 : forall a, 0 <= a < 2 ^ 64 -> ~ (z_ctx cx + 60 <= a < z_ctx cx + 68) -> mbyte trasegs (mrestrict Hh mb) a = mbyte trasegs (mrestrict Hh ma) a)
by (intros a Ha Hu;
eapply (aframe_mbyte_list Ef _ _ _ [(z_ctx cx + 60, z_ctx cx + 68); (0, 0)] a HFr Ha);
[ apply Forall2_cons; [right; cbn [fst snd YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi actx_region base_val ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8, unsigned_lit_small by lia; lia |];
apply Forall2_cons; [left; cbn; lia | apply Forall2_nil]
| cbn; split; [exact Hu | split; [lia | exact I]] ]);
clear HFr; try match goal with H : frame_of _ _ _ _ |- _ => clear H end
end.
fold_step T5 HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 320)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv24 : ew Ev 23 = Z_to_bv 64 s') by (rewrite (AG 23%nat) by lia; exact HE23)
end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA (repeat 0 (Z.to_nat (z_idl cx * z_idl cx))) (repeat 0 4096) (repeat 0 4096) TM s' (lp + 2) (z_idl cx + 2) 1 (Cn + 1) (R + 1)) end.
split; [unfold atail_pc; cbn [la_s]; replace (s' <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ5|].
split; [intros a Ha; apply HK; [lia | unfold rst_untouched; repeat split; lia]|].
pose proof (inv_reset (z_idl cx) (z_nP cx) Hidl _ (s' - 1) HI ltac:(cbn [la_dp]; exact Hdp) ltac:(cbn [la_s]; lia)) as HI'.
cbn [st_reset] in HI'. replace (s' - 1 + 1) with s' in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM]. split; [|reflexivity].
split.
{ split; [|split; [aregv HS (30%bv : bv 5) | aregv HS (16%bv : bv 5)]].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia] end. }
split; [genM 0%nat HS HEv8 HG ltac:(fun a Ha => apply HK; [lia | unfold rst_untouched; septac HSEP 1%nat 6%nat; septac HSEP 2%nat 6%nat; septac HSEP 3%nat 6%nat; septac HSEP 4%nat 6%nat; repeat split; lia])
(z_ctx cx) (SOff 33 1) (lp + 2) HE33 (SOff 34 0) (z_idl cx + 2) HE34 (SOff 35 0) 1 HE35|].
split.
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- apply arr16_zeros_aview. intros a Ha. rewrite Z2Nat.id in Ha by lia. apply ZTI; [lia | unfold in_rng; lia].
- apply arr16_zeros_aview. intros a Ha. cbn in Ha. apply ZLM; [lia | unfold in_rng; lia].
- apply arr16_zeros_aview. intros a Ha. cbn in Ha. apply ZLI; [lia | unfold in_rng; lia].
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply HK; [lia|]. unfold rst_untouched. septac HSEP 5%nat 6%nat. septac HSEP 1%nat 5%nat. septac HSEP 2%nat 5%nat. septac HSEP 3%nat 5%nat. septac HSEP 4%nat 5%nat.
repeat split; lia. }
split; [exact HI'|]. split; [aregv HS (23%bv : bv 5) | lia].
-
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_RST2) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_RST2) memT (seg_rom trasegs))) in HJ.
stretch cx HS HJ SHOK AG HE8 Actx HBg HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
mcall cx HS HJ AG HE53 HE2 HE3 HE4 Hzgp Hztp (z_ti cx) (2 * z_idl cx * z_idl cx) 0x89ffc HBti Ati.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff1 & Hfr1 & Hpres2).
reseat HS HJ2 HP2 [0; 1]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [try rewrite (AG 8%nat) by lia; rewrite HE8 | try rewrite (AG 2%nat) by lia; rewrite HE2];
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr1; [lia | revert Ha; first [sep HSEP 1%nat 6%nat | lia] | unfold ESTACK; lia]
| exact Hpres2 ]).
mpost cx Heff1 Hfr1 (z_ti cx) (2 * z_idl cx * z_idl cx) ZTI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 0x89ffc) mem2 (seg_rom trasegs))) in HJ2. reshok_bx HS 27%nat.
stretch cx HS HJ2 SHOK AG HE8 Actx HBg HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
mcall cx HS HJ2 AG HE54 HE2 HE3 HE4 Hzgp Hztp (z_lm cx) 8192 0x8a014 HBlm Alm.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff2 & Hfr2 & Hpres3).
reseat HS HJ3 HP3 [0; 1]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [rewrite (AG 8%nat) by lia; rewrite HE8 | rewrite (AG 2%nat) by lia; rewrite HE2];
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr2; [lia | revert Ha; first [sep HSEP 2%nat 6%nat | lia] | unfold ESTACK; lia]
| exact Hpres3 ]).
mpost cx Heff2 Hfr2 (z_lm cx) 8192 ZLM HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 0x8a014) mem3 (seg_rom trasegs))) in HJ3. reshok_bx HS 27%nat.
stretch cx HS HJ3 SHOK AG HE8 Actx HBg HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
mcall cx HS HJ3 AG HE55 HE2 HE3 HE4 Hzgp Hztp (z_lc cx) 4096 0x8a030 HBlc Alc.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff3 & Hfr3 & Hpres4).
reseat HS HJ4 HP4 [0; 1]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [rewrite (AG 8%nat) by lia; rewrite HE8 | rewrite (AG 2%nat) by lia; rewrite HE2];
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr3; [lia | revert Ha; first [sep HSEP 3%nat 6%nat | lia] | unfold ESTACK; lia]
| exact Hpres4 ]).
mpost cx Heff3 Hfr3 (z_lc cx) 4096 ZLC HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 0x8a030) mem4 (seg_rom trasegs))) in HJ4. reshok_bx HS 27%nat.
stretch cx HS HJ4 SHOK AG HE8 Actx HBg HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
mcall cx HS HJ4 AG HE56 HE2 HE3 HE4 Hzgp Hztp (z_li cx) 8192 0x8a04c HBli Ali.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff4 & Hfr4 & Hpres5).
reseat HS HJ5 HP5 [0; 1]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [rewrite (AG 8%nat) by lia; rewrite HE8 | rewrite (AG 2%nat) by lia; rewrite HE2];
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr4; [lia | revert Ha; first [sep HSEP 4%nat 6%nat | lia] | unfold ESTACK; lia]
| exact Hpres5 ]).
mpost cx Heff4 Hfr4 (z_li cx) 8192 ZLI HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 0x8a04c) mem5 (seg_rom trasegs))) in HJ5. reshok_bx HS 27%nat.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEw8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEw27 : ew Ev 27 = Z_to_bv 64 SB) by (rewrite (AG 27%nat) by lia; exact HE27) end.
aj_run_to_tok tratbl_lib_ok HS HJ5 SHOK Bspan PC_HEAD; try (oblk HJ5 HBg HEw8 HEw27 (z_ctx cx)).
clear HEw8 HEw27.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (z_ctx cx));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia
| cbn [YQ0b.r_wlo YQ0b.r_whi actx_region]; intros a Ha; replace a with (z_ctx cx + (a - z_ctx cx)) by lia; apply Actx; [exact HBg | lia]
| apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ]. }
lazymatch goal with HFr : frame_of ?Ef _ (mrestrict ?Hh ?ma) (mrestrict _ ?mb) |- _ =>
assert (T5 : forall a, 0 <= a < 2 ^ 64 -> ~ (z_ctx cx + 60 <= a < z_ctx cx + 68) -> mbyte trasegs (mrestrict Hh mb) a = mbyte trasegs (mrestrict Hh ma) a)
by (intros a Ha Hu;
eapply (aframe_mbyte_list Ef _ _ _ [(z_ctx cx + 60, z_ctx cx + 68); (0, 0)] a HFr Ha);
[ apply Forall2_cons; [right; cbn [fst snd YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi actx_region base_val ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia; try rewrite (AG 8%nat) by lia; rewrite HE8, unsigned_lit_small by lia; lia |];
apply Forall2_cons; [left; cbn; lia | apply Forall2_nil]
| cbn; split; [exact Hu | split; [lia | exact I]] ]);
clear HFr; try match goal with H : frame_of _ _ _ _ |- _ => clear H end
end.
fold_step T5 HSEP Rti2 Rlm2 Rlc2 Rli2 Hsplo.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 320)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv24 : ew Ev 23 = Z_to_bv 64 s') by (rewrite (AG 23%nat) by lia; exact HE23)
end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA (repeat 0 (Z.to_nat (z_idl cx * z_idl cx))) (repeat 0 4096) (repeat 0 4096) TM s' (lp + 2) (z_idl cx + 2) 1 (Cn + 1) (R + 1)) end.
split; [unfold atail_pc; cbn [la_s]; replace (s' <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ5|].
split; [intros a Ha; apply HK; [lia | unfold rst_untouched; repeat split; lia]|].
pose proof (inv_reset (z_idl cx) (z_nP cx) Hidl _ (s' - 1) HI ltac:(cbn [la_dp]; exact Hdp) ltac:(cbn [la_s]; lia)) as HI'.
cbn [st_reset] in HI'. replace (s' - 1 + 1) with s' in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM]. split; [|reflexivity].
split.
{ split; [|split; [aregv HS (30%bv : bv 5) | aregv HS (16%bv : bv 5)]].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia] end. }
split; [genM 0%nat HS HEv8 HG ltac:(fun a Ha => apply HK; [lia | unfold rst_untouched; septac HSEP 1%nat 6%nat; septac HSEP 2%nat 6%nat; septac HSEP 3%nat 6%nat; septac HSEP 4%nat 6%nat; repeat split; lia])
(z_ctx cx) (SOff 33 1) (lp + 2) HE33 (SOff 34 0) (z_idl cx + 2) HE34 (SOff 35 0) 1 HE35|].
split.
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- apply arr16_zeros_aview. intros a Ha. rewrite Z2Nat.id in Ha by lia. apply ZTI; [lia | unfold in_rng; lia].
- apply arr16_zeros_aview. intros a Ha. cbn in Ha. apply ZLM; [lia | unfold in_rng; lia].
- apply arr16_zeros_aview. intros a Ha. cbn in Ha. apply ZLI; [lia | unfold in_rng; lia].
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply HK; [lia|]. unfold rst_untouched. septac HSEP 5%nat 6%nat. septac HSEP 1%nat 5%nat. septac HSEP 2%nat 5%nat. septac HSEP 3%nat 5%nat. septac HSEP 4%nat 5%nat.
repeat split; lia. }
split; [exact HI'|]. split; [aregv HS (23%bv : bv 5) | lia].
Qed.
End S.
End b.
