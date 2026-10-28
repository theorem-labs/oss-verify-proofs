(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI59 YI0x UI57 UI1h UI1g UI16 YI08 UI3d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis CLOSE : close_spec API.
Definition ss_rgb_close : sstate :=
mkSS ubs2_A_cgif_rgb_close sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 RGB_SIZE 0 0 (obj_chunks_from LAY_Rgb 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RGBCLOSE_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - RGB_SIZE) 4) ] [] []).
Theorem ubs2_rgb_close : rgb_close_spec API.
Proof.
intros L A regs mem md r rv g s N bef nbef rest HPRE Hid Ha0 Hobj Hg Hbef Hat Hwf HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : RGBCLOSE_STK = 9760) by reflexivity. assert (HCSv : CLOSE_STK = 9728) by reflexivity.
assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HRSv : RGB_SIZE = 64) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hrin : In (r, RGB_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md r RGB_SIZE HH Hrin ltac:(lia)) as (Rr0 & Rr1 & Rr16).
pose proof (obj_at_nth ubs2segs mem r LAY_Rgb rv RG_gif _ _ Hobj eq_refl Hg) as [_ Rg]. cbn [snd] in Rg.
pose proof (obj_at_nth ubs2segs mem r LAY_Rgb rv RG_bef _ _ Hobj eq_refl Hbef) as [_ Rbef]. cbn [snd] in Rbef.
assert (HB' : Permutation (blocks L A) (cgif_blocks g s N ++ (r, RGB_SIZE) :: optb bef nbef ++ rest)).
{ eapply Permutation_trans; [exact HB | apply Permutation_middle]. }
destruct (af_cgif_geom API L A mem md g s N _ HH HB') as (_ & _ & (Hg0 & Hg1 & Hg16)).
set (E := Ereg regs (map (Z_to_bv 64) rv ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error rv j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = r) by (rewrite (HE 10%nat 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
assert (HE32 : ew E 32 = Z_to_bv 64 g) by (apply (HV 0%nat); exact Hg).
assert (HE41 : ew E 41 = Z_to_bv 64 bef) by (apply (HV 9%nat); exact Hbef).
assert (Hspm : (spZ regs - 32) mod 16 = 0) by (replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (sp0 := spZ regs) in *.
assert (HS : st_ok ubs2segs E ss_rgb_close (mkst regs (Z_to_bv 64 ubs2_A_cgif_rgb_close) mem (seg_rom ubs2segs))).
{ unfold ss_rgb_close. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ mem 2 sp0); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ eapply (region_ok_obj ubs2segs _ mem 10 r); [exact HU10 | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10.
change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs2_msyms MR RGBCLOSE_STK
((r, r + RGB_SIZE) :: blocks_fp (cgif_blocks g s N) ++ optfp bef nbef) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_cgif_rgb_close) mem (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cgif_close.
{ wr_ok_tac. exact HU2. }
jreg HS (10%bv:reg) as Hr10. rewrite HE32 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2. replace (sp0 + -32) with (sp0 - 32) in Hr2 by lia.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
cbn [ms_mem mkst] in HF.
assert (Hspms : spZ (ms_regs ms) = sp0 - 32) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := CLOSE_STK) (FP1 := blocks_fp (cgif_blocks g s N))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) =>
Permutation (blocks L5 A5) ((r, RGB_SIZE) :: optb bef nbef ++ rest));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hspm | lia
| rewrite Hspms; lia
| rewrite Hspms; lia | exact Hr4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (CLOSE _ _ _ _ _ g s N ((r, RGB_SIZE) :: optb bef nbef ++ rest) HPRE1 Hid Hr10); [| exact Hwf | exact HB'].
eapply (cgif_at_low API); [exact HH | exact HB' | exact Hat |]. intros a Ha.
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. left. split.
+ destruct Ha as (rr & Hrr & Harr). exists rr. split; [right; apply in_app_iff; left; exact Hrr | exact Harr].
+ apply inFP_blocks_fp in Ha as (b & n & Hbn & Habn).
assert (Hbin : In (b, n) (blocks L A)) by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; left; exact Hbn]).
destruct (blocks_range _ _ LAWS L A mem md b n HH Hbin) as [_ R1]. lia. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5.
pose proof HJc5 as (_ & _ & Hhi5 & Hblk5 & _).
assert (Hr5 : In (r, RGB_SIZE) (blocks L5 A5)) by (eapply blocks_perm_in; [exact HB5 | left; reflexivity]).
assert (KR : forall i, 0 <= i < RGB_SIZE -> mbyte ubs2segs mem5 (r + i) = mbyte ubs2segs (ms_mem ms) (r + i)).
{ intros i Hi. apply (Hblk5 r RGB_SIZE i Hrin Hr5 Hi). intros HF1.
apply inFP_blocks_fp in HF1 as (b & n & Hbn & Habn).
pose proof (heap_sep_app API L A mem md (cgif_blocks g s N) ((r, RGB_SIZE) :: optb bef nbef ++ rest) (b, n) (r, RGB_SIZE) HH HB' Hbn ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep. destruct (blocks_range _ _ LAWS L A mem md b n HH ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; left; exact Hbn])) as [Rb0 Rb1]. lia. }
jafter_call_keep HS 44%nat regs5 mem5 HP5 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi5 | lia | lia | rewrite Hspms; lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs2segs _ _ _ 10); [exact HU10 | intros a Ha; replace a with (r + (a - r)) by lia; apply KR; cbn in Ha; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ5 ubs2_A_free.
{ wr_ok_tac. ew_havoc. exact HU2. }
jreg HS (10%bv:reg) as Hq10. rewrite HE41 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite HU2 in Hq2. replace (sp0 + -32) with (sp0 - 32) in Hq2 by lia.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API))
with (p := bef) (n := nbef) (rest := (r, RGB_SIZE) :: rest) (spc := sp0 - 32);
[ exact HS | reflexivity | reflexivity | exact HJ5 | eapply Permutation_trans; [exact HB5 | apply Permutation_middle]
| exact Hq10 | exact Hq2 | lia | exact Hspm | lia | lia | exact Hq4 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hb0 _ i Hi. exists (bef, bef + nbef). split; [| cbn; lia].
right. apply in_app_iff. right. unfold optfp. rewrite (proj2 (Z.eqb_neq _ _) Hb0). left. reflexivity. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & HB6 & Hkeep6 & Hhi6). clear HJ5.
assert (Hr6 : In (r, RGB_SIZE) (blocks L6 A6)) by (eapply blocks_perm_in; [exact HB6 | left; reflexivity]).
jafter_call_keep HS 60%nat regs6 mem6 HP6 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hr6 | exact Hkeep6 | cbn; lia | cbn; lia | cbn; lia]. }
clear HS Hhi6 Hkeep6 Hq10 Hq2 Hq4 Hq1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ6 ubs2_A_free.
{ wr_ok_tac. ew_havoc. exact HU2. }
jreg HS (10%bv:reg) as Hq10. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 10)), HU10 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite HU2 in Hq2. replace (sp0 + -32) with (sp0 - 32) in Hq2 by lia.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS ubs2_errno_low IMG (aa_free API)) with (a := r) (n := RGB_SIZE) (spc := sp0 - 32);
[ exact HS | reflexivity | reflexivity | exact HJ6 | exact Hr6 | exact Hq10 | exact Hq2 | lia | exact Hspm | lia | lia
| exact Hq4 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros _ i Hi. exists (r, r + RGB_SIZE). split; [left; reflexivity | cbn; lia]. }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Hrm7 & Hkeep7 & Hhi7 & _). clear HJ6.
jafter_call_keep HS 76%nat regs7 mem7 HP7 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi7 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS Hhi7 Hkeep7 Hq10 Hq2 Hq4 Hq1. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ7.
{ wr_ok_tac. ew_havoc. exact HU2. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ7))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ7)))). }
lazymatch type of HS with st_ok _ _ _ ?msf => exists L7, A7, (ms_regs msf), (ms_mem msf), md7 end.
split.
{ cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite !ew_havoc_old in Q1 by (cbv; lia); rewrite ?Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra; reflexivity end. }
split; [exact HJ7|].
split.
{ pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 76 _ _ _ ltac:(lia)
(env_agree_havoc_ge 32 60 _ _ _ ltac:(lia)
(env_agree_havoc_ge 32 44 _ _ _ ltac:(lia) (env_agree_refl _ _)))) ltac:(vm_compute; reflexivity)) as HPR.
exact HPR. }
eapply perm_after_rm1; [exact HB6 | exact Hrm7].
Qed.
End S.
End c.
