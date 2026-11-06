(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YCct YC4z YCcq YCcp YCcv YCcu YCcw YCcr YCcy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Lemma rf_C : rf_from B ss_RET (INV_RET B) -> rf_from B ss_C (INV_C B).
Proof.
intros RRET. rf_prelude.
pose proof HINV as (Hk0 & fmt & img & HENO & HIMG). pose proof HIMG as (Efmt & Hfmt & Eimg & Hr4096 & HrHi & HrCeil & Hr16 & Ebl & Timg & Aimg).
cbn [x_N x_lyc x_Sc x_FP x_ly x_S x_STK x_sp0 x_own x_cur x_nb] in HENO, Efmt, Hfmt, Eimg, Hr4096, HrHi, HrCeil, Hr16, Ebl, Timg, Aimg.
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Ebl; apply in_app_iff; left; exact Hpdc).
assert (HrIn : In (img, fmt * N) (ablocks B ly3 S3)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((img, fmt * N) :: Bb)).
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply Permutation_cons; [reflexivity | exact HPerm]. }
assert (HfN : 3 <= fmt * N <= 40000) by (unfold RGB_NMAX in HN; clear - HN Hfmt; nia).
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as [HrqN1 HrqN2].
assert (HsepB : forall b m, In (b, m) Bb -> img + req_size (fmt * N) <= b \/ b + req_size m <= img).
{ intros b m Hb. destruct (in_split _ _ Hb) as (l1' & l2' & El).
assert (HP' : Permutation (ablocks B ly3 S3) ((img, fmt * N) :: (b, m) :: l1' ++ l2')).
{ eapply Permutation_trans; [exact HPerm3|]. apply perm_skip. rewrite El. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ _ _ _ HAR3 HP') as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. clear - D. lia. }
assert (HimgFS : forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ (img <= a < img + fmt * N)).
{ intros c p a Hcp Ha Hin. destruct Ha as [Ha | Ha].
+ pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ img (fmt * N) c p HAR3 HrIn ltac:(rewrite Hfrs3; exact Hcp)) as D.
rewrite EFA3 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin HrqN2. lia.
+ destruct (frames_bounds trasegs B LAWS _ _ _ _ _ c p HAR3 ltac:(rewrite Hfrs3; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA3 in F0, Fc, Fh.
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin HrHi HrqN2 C2 C3. lia. }
assert (HimgF : forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ (img <= a < img + fmt * N)).
{ intros a Ha. apply (HimgFS cid pos a Hfin). left. unfold in_zr, frame_rng. cbn [fst snd]. exact Ha. }
pose proof (HsepB pdata nb Hpd) as Hdisj. rbox Hdisj.
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RBspan.
all: try (oblsA HJ3 Hpd3 HRAst HRAdst E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA3. }
rf_after_run Usp B10 B11.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb (proj1 HJ3) Hpd3) as (_ & _ & _ & _ & Hppres3 & _).
rreg HS (10%bv : bv 5) Ra0. rregD HS (11%bv : bv 5) Ra1. rregD HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
ly3 S3 _ kk img (pdata + (cur + 7)) (fmt * N) (spZ regs - 128 - sp0) (Z_to_bv 64 0x819ac) HJ3);
[ rewrite Ra0; enorm; exact Eimg
| rewrite Ra1; rewrite denot_lit_U; unfold w64; f_equal;
lazymatch goal with |- context [U ?Ex _] => rewrite (U_atom_off Ex 36 (pdata + cur) 7 ltac:(enorm; exact E36)) by lia end; clear; lia
| rewrite Ra2; rewrite denot_lit_U; unfold w64; f_equal; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw];
lazymatch goal with |- context [U ?Ex (SOff 12 0)] => rewrite (U_lit Ex 0) by lia; rewrite (U_atom Ex 12 N ltac:(enorm; exact E12)), (U_atom Ex 86 fmt ltac:(enorm; exact Efmt)) by (unfold RGB_NMAX in HN; lia) end;
rewrite (zcanon_id (N * fmt)) by (unfold M64; clear - HfN; lia); rewrite Z.add_0_r; rewrite zcanon_id by (unfold M64; clear - HfN; lia); clear; lia
| clear - HfN; lia | clear - Hr4096; lia | clear - HrCeil HrqN2 C1; lia
| unfold spZ; rewrite Rsp; enorm; rewrite Usp; fold (spZ regs); rewrite unsigned_lit_small by (clear - HSPB HTS Has C1; lia); clear; lia
| replace (spZ regs - 128 - sp0) with (spZ regs - sp0 + (-8) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| clear - Hwhi; lia
| unfold ESTACK; clear - Hwlo HTS Has; lia
| rewrite Rgp; enorm; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; enorm; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| intros a Ha; split; [replace a with (img + (a - img)) by lia; apply Aimg; [exact HrIn | lia] | unfold ESTACK; intro; lia]
| apply (amem_range_of_block trasegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) HrIn); lia
| apply (range_addressable_of_block trasegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) HrIn); lia
| intros _; apply (shadow_hull_vis_of_block trasegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) HrIn); lia
| split; [lia|]; split; [lia|]; split;
[ intros a Ha; split; [| unfold spZ, ESTACK; rewrite Rsp; enorm; rewrite Usp; fold (spZ regs); rewrite unsigned_lit_small by lia; intro; lia];
apply (aview_some_of_apresent trasegs); apply (proj1 (Hppres3 a ltac:(lia)))
| split; [clear - Hdisj HENO Hcur HrqN2 Hrq2; unfold rboxed in Hdisj; lia|];
split; [apply (amem_range_of_block trasegs B LAWS ly3 S3 W3 _ _ pdata nb _ _ (proj1 HJ3) Hpd3); lia|]; split;
[ apply (range_addressable_of_block trasegs B LAWS ly3 S3 W3 _ _ pdata nb _ _ (proj1 HJ3) Hpd3); lia
| intros _; apply (shadow_hull_vis_of_block trasegs B LAWS ly3 S3 W3 _ _ pdata nb _ _ (proj1 HJ3) Hpd3); lia ] ] ] end. }
cbv beta. clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff4 & Hfr4 & Hpres4).
replace (sp0 + (spZ regs - 128 - sp0)) with (spZ regs - 128) in Hfr4 by lia.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ4)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
lazymatch goal with HK : rfc_kept _ _ W3 (ms_mem ?msX) _ _ _ _ _ _ |- _ =>
pose proof (rfc_kept_stepE _ _ _ _ _ _ _ _ _ _ _ (fun a => (img <= a < img + fmt * N) \/ (spZ regs - 128 - ESTACK <= a < spZ regs - 128)) (fun a => img <= a < img + fmt * N) HK HSEP
ltac:(intros a Ha Hn; apply Hfr4; [exact Ha | clear - Hn; tauto | clear - Hn; tauto])
ltac:(intros a Ha; cbn beta in *; clear - Ha HTS Has; unfold ESTACK in Ha; lia) ltac:(clear - HSPB; lia)
ltac:(intros a Ha; cbn beta in *; clear - Ha HrCeil HrqN2; lia)
ltac:(intros b m i Hb Hi Hin; cbn beta in *; pose proof (HsepB b m Hb); clear - Hi Hin H HrqN2; lia)
HimgFS) as KEPT4;
assert (SHK4 : forall a, 2147450880 <= a < kHighShadowEnd -> aview trasegs (w_H W3) mem4 a = aview trasegs (w_H W3) (ms_mem msX) a)
by (intros a Ha; apply Hfr4; [clear - Ha C1 C2 C3 C4 C5; lia | clear - Ha HrHi HrqN2 C1 C2 C3; lia | clear - Ha HSPB C1 C2 C3 HTS Has; unfold ESTACK; lia]);
clear HK end.
pose proof (RA_kept_low _ _ dst 24 SHK4 ltac:(lia) ltac:(lia) HRAdst) as RAdst4.
pose proof (RA_kept_low _ _ st 24 SHK4 ltac:(lia) ltac:(lia) HRAst) as RAst4.
clear HRAdst HRAst SHK4.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4]%nat AG
ltac:(first [ eapply region_kept_aview;
[ evalER AG
| intros a Ha; apply Hfr4;
[ clear - Ha HSPB HSTB HDSTB HTS Has C1 C3; lia
| first [ clear - Ha HSPB HSTB HrCeil HrqN2 HTS Has; lia | intros X; apply (HimgF a); [clear - Ha Hdst1 Hdst2; lia | clear - X HrqN2; lia] ]
| clear - Ha HSPB HSTB HDSTB HTS Has; unfold ESTACK; lia ]
| exact Hpres4 ]
| apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword trasegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2) | lia]
| apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword trasegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK RBspan 0x81988.
all: try (oblsA HJ4 Hpd3 RAst4 RAdst4 E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA3. }
rf_after_run Usp B10 B11.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rreg HS (10%bv : bv 5) Ra0.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E12n : ew Ev 12 = Z_to_bv 64 N) by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact G12) end.
rf_stream_words HS B10 E33 E34 (cur + 7 + fmt * N)
ltac:(rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw];
lazymatch goal with |- context [U ?Ex (SOff 12 0)] => rewrite (U_atom_off Ex 35 cur 7 E35), (U_atom Ex 12 N E12n), (U_atom Ex 86 fmt Efmt) by (unfold RGB_NMAX in HN; lia) end;
rewrite (zcanon_id (N * fmt)) by (unfold M64; clear - HfN; lia); rewrite zcanon_id by (unfold M64; clear - HfN Hcur HnbM; lia); clear; lia) Vp Vn Vc.
rf_obj_at HS B11 img ltac:(rewrite sv_denot_SOff0; exact Eimg) fmt ltac:(rewrite sv_denot_SOff0; exact Efmt) OBJ.
rfj_join HS ss_RET 310%nat rf_RET_deads_bv.
rf_hand RRET HS.
split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists 1, (cur + 7 + fmt * N).
split; [exact Ra0|]. split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [clear - Hcur HENO HfN; lia|].
right. right. split; [reflexivity|]. destruct OBJ as (fattr & fgen & delay & OBJ). exists img, fmt, fattr, fgen, delay.
split; [exact Hfmt|]. split; [exact OBJ|]. split; [exact HPerm3|]. split; [exact Timg|].
intros blc i Hblc Hi. exact (Aimg blc i ly3 Hblc Hi).
Qed.
End e.
End d.
