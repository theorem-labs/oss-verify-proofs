(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI57 UI1h YI0x YI07 YP14 YI08 YI0c YI0g
UI3h UI3d UI4v UIZm.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma optfp_fp : forall p n, optfp p n = blocks_fp (optb p n).
Proof. intros p n. unfold optfp, optb, blocks_fp. destruct (p =? 0); reflexivity. Qed.
Definition LAY_XC : layout_t := [(48, 8%N)].
Definition LAY_XD : layout_t := [(48, 8%N)].
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis FCHT : forall fx', free_cht_spec (fx:=fx') API.
Hypothesis FTREE : forall fx', free_tree_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation keep2 pnew fimg := (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]).
Let tmp_of_station := UIZm.tmp_of_station API L A r g bef beffmt s N img fmt rest.
Let kept_across_call := UIZm.kept_across_call API.
Let init_of_live_r := UIZm.init_of_live_r API r g bef beffmt s N img fmt rest.
Definition ss_X38 : sstate := mkSS PC_X38 sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma ubs2_rgbadd_X38 : seg_X38 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KXB regs1 Lc Ac memc mdc pnew fimg c f h u p x cnt0 ts0 HAT.
destruct HAT as (HINV & HREGS & Hfmt & G20 & G18 & G9 & G8 & G21 & Hobj & Hcg & Hpnew & Hfimg & Hcht & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCSv : CHT_SIZE = 48) by reflexivity. assert (HFSv : FREECHT_STK = 8208) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
set (tmp := (c, CHT_SIZE) :: optb f (4 * TS0) ++ optb h (3 * TS0) ++ optb u TS0 ++ optb p (3 * TS0) ++ optb x (4 * TS0)).
assert (HB' : Permutation (blocks Lc Ac) (keep2 pnew fimg ++ tmp)).
{ eapply Permutation_trans; [exact HB|]. subst tmp. rewrite <- !app_assoc. apply Permutation_refl. }
assert (HBc : Permutation (blocks Lc Ac) ((c, CHT_SIZE) :: optb f (4 * TS0) ++ optb h (3 * TS0) ++ optb u TS0 ++ optb p (3 * TS0) ++ optb x (4 * TS0) ++ keep2 pnew fimg)).
{ eapply Permutation_trans; [exact HB'|]. eapply Permutation_trans; [apply Permutation_app_comm|]. subst tmp. cbn [app]. rewrite <- !app_assoc. apply Permutation_refl. }
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 (keep2 pnew fimg)) by (intros x0 Hx0; apply in_app_iff; left; exact Hx0).
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E ss_X38 (mkst regs1 (Z_to_bv 64 PC_X38) memc (seg_rom ubs2segs))).
{ unfold ss_X38. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_X38) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free_col_hash_table. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hr10. rewrite (HE 20%nat 20%bv eq_refl), G20 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECHT_STK)
(FP1 := (c, c + CHT_SIZE) :: optfp f (4 * TS0) ++ optfp h (3 * TS0) ++ optfp u TS0 ++ optfp p (3 * TS0) ++ optfp x (4 * TS0))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) (keep2 pnew fimg));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm in HPRE1 |- *. eapply SR_mono.
{ eapply (FCHT fx Lc Ac (ms_regs ms) memc mdc c f h u p x cnt0 ts0 (4 * TS0) (3 * TS0) TS0 (3 * TS0) (4 * TS0) (keep2 pnew fimg) HPRE1 Hr10 Hcht HBc). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right.
assert (Ha' : inFP (blocks_fp tmp) a).
{ subst tmp. cbn [blocks_fp map fst snd]. rewrite !map_app. change (map ?F (optb ?q ?n)) with (blocks_fp (optb q n)). rewrite <- !optfp_fp. exact Ha. }
apply inFP_blocks_fp in Ha' as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station Lc Ac memc mdc (keep2 pnew fimg) tmp b n HHc HB' HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte ubs2segs mem5 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep' : forall b m i, In (b, m) (keep2 pnew fimg) -> 0 <= i < m -> mbyte ubs2segs mem5 (b + i) = mbyte ubs2segs memc (b + i)).
{ rewrite <- Hmm. eapply (kept_across_call FREECHT_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L5 A5 mem5 md5 (keep2 pnew fimg) tmp);
[rewrite Hmm; exact HHc | exact HB' | | exact HB5].
subst tmp. cbn [blocks_fp map fst snd]. rewrite !map_app. change (map ?F (optb ?q ?n)) with (blocks_fp (optb q n)). rewrite <- !optfp_fp. exact HJc5. }
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XB) end.
apply (KXB regs5 L5 A5 mem5 md5 pnew fimg).
split.
{
split; [exact HJ5|]. split; [exact (init_of_live_r L5 A5 mem5 md5 _ (proj1 HJ5) HB5)|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem5 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [rewrite (regs_preserved_frame _ _ HP5 2%bv ltac:(vm_compute; reflexivity)); exact Hr2|].
split; [rewrite (regs_preserved_frame _ _ HP5 3%bv ltac:(vm_compute; reflexivity)); jreg HS (3%bv:reg) as Hq3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hq3; exact Hq3|].
rewrite (regs_preserved_frame _ _ HP5 4%bv ltac:(vm_compute; reflexivity)), Hr4, Htp0. reflexivity. }
split; [exact Hfmt|].
split. { rewrite (regs_preserved_frame _ _ HP5 18%bv ltac:(vm_compute; reflexivity)). jreg HS (18%bv:reg) as Hq. rewrite (HE 18%nat 18%bv eq_refl), G18 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 9%bv ltac:(vm_compute; reflexivity)). jreg HS (9%bv:reg) as Hq. rewrite (HE 9%nat 9%bv eq_refl), G9 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 21%bv ltac:(vm_compute; reflexivity)). jreg HS (21%bv:reg) as Hq. rewrite (HE 21%nat 21%bv eq_refl), G21 in Hq. exact Hq. }
split. { rewrite (regs_preserved_frame _ _ HP5 8%bv ltac:(vm_compute; reflexivity)). jreg HS (8%bv:reg) as Hq. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hq. exact Hq. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i); [apply in_app_iff; left; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N (keep2 pnew fimg)); [| exact Hcg | exact Hkeep'].
unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split; [exact Hpnew|]. split; [exact Hfimg|]. exact HB5.
Qed.
Section j.
Context {fxi : YK11.FPState}.
Definition ss_XD : sstate :=
mkSS PC_XD sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 (obj_chunks_from LAY_XD 32) ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XD_at : forall regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn,
K_XC (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XD (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XD) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn KXC HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & G24 & G18 & G20 & G21 & G8 & S48 & Hobj & Hcg & Hchq & Hpnew & Hfimg & Hfdp & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HCSv : CHT_SIZE = 48) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
set (keep := keep2 pnew fimg ++ cht_blks C).
assert (HB' : Permutation (blocks Lc Ac) ((fdp, fdn) :: keep)).
{ eapply Permutation_trans; [exact HB|].
replace (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, fdn)]) with (keep ++ [(fdp, fdn)])
by (subst keep; rewrite <- !app_assoc; reflexivity).
apply Permutation_sym, Permutation_cons_append. }
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 keep)
by (intros x0 Hx0; subst keep; apply in_app_iff; left; apply in_app_iff; left; exact Hx0).
assert (Hfin : In (fdp, fdn) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB' | left; reflexivity]).
assert (Hfiin : In (fimg, N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB' | right; subst keep; apply in_app_iff; left; apply in_app_iff; right; right; left; reflexivity]. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc fimg N HHc Hfiin ltac:(lia)) as (Hfi0 & Hfi1 & _).
assert (HoXD : obj_at ubs2segs memc (sp regs0) LAY_XD [fimg]).
{ cbn [obj_at LAY_XD].
split; [split; [cbn [fst snd]; apply val_mem_word_mem; exact S48 | cbn [fst snd]; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia]|]. exact I. }
set (E := Ereg regs1 (map (Z_to_bv 64) [fimg] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) ubs2segs E ss_XD (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XD) memc (seg_rom ubs2segs))).
{ unfold ss_XD. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj ubs2segs _ memc 2 (sp regs0)); [exact HU2 | unfold sp, sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HoXD | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs1 _ [] jj v Hjj).
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XD) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
clear HF HG.
jreg HS (10%bv:reg) as Hq10. rewrite (HE 24%nat 24%bv eq_refl), G24 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hq2.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), G4 in Hq4.
jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS ubs2_errno_low IMG (aa_free API)) with (a := fdp) (n := fdn) (spc := sp regs0);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hfin | exact Hq10 | exact Hq2
| unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hq4; exact Htp0 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin0 i Hi. exfalso.
refine (proj2 (tmp_of_station Lc Ac memc mdc keep [(fdp, fdn)] fdp fdn HHc _ HBent Hsub ltac:(left; reflexivity) ltac:(lia)) Hin0).
eapply Permutation_trans; [exact HB' | apply Permutation_cons_append]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hinit2).
pose proof (perm_after_rm1 _ _ _ _ HB' Hrm) as HB2.
rewrite Hmm in Hkeep, Hhi2.
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte ubs2segs mem2 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hsx. apply (proj1 (Hhi2 x0 Hx ltac:(lia))). }
assert (Hkeep' : forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. apply (Hkeep b m i); [| exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB2 | exact Hbm]. }
jafter_call_keep HS 33%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | rewrite Hmm; exact Hhi2 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | lia | cbn; lia | cbn; lia]. }
clear HS Hq10 Hq2 Hq4 Hq1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ2 PC_XC. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_regs ms_mem mkst] in HF, HJ2.
assert (Hmm2 : ms_mem ms0 = mem2) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XC) end. rewrite Hmm2. rewrite Hmm2 in HJ2.
apply (KXC fxi (ms_regs ms0) L2 A2 mem2 md2 ha pnew fimg C cnt pal HFRM).
split.
{
split; [exact HJ2|]. split; [exact Hinit2|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem2 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [exact Hfmt|].
split; [jreg HS (20%bv:reg) as Hq; rewrite Hq, (HE 20%nat 20%bv eq_refl); exact G20|].
split; [jreg HS (18%bv:reg) as Hq; rewrite Hq, (HE 18%nat 18%bv eq_refl); exact G18|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
split; [jreg HS (21%bv:reg) as Hq; rewrite Hq, (HE 21%nat 21%bv eq_refl); exact G21|].
split. { eapply slot_kept; [exact S48 | unfold SL_fimg; lia | unfold sp, sp0, RGBA_FRAME in *; lia | unfold SL_fimg, sp, sp0, RGBA_FRAME in *; lia | exact HI]. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i); [subst keep; apply in_app_iff; left; apply in_app_iff; left; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N keep); [| exact Hcg | exact Hkeep'].
subst keep. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { eapply chtq_ok_kept; [exact Hchq | |].
- intros i Hi. apply (Hkeep' (ch_c C) CHT_SIZE i); [subst keep; apply in_app_iff; right; left; reflexivity | exact Hi].
- intros i Hi. apply (Hkeep' (ch_p C) (3 * ch_T C) i); [subst keep; apply in_app_iff; right; right; right; right; right; left; reflexivity | exact Hi]. }
split; [exact Hpnew|]. split; [exact Hfimg|]. subst keep. rewrite <- app_assoc in HB2. exact HB2.
Qed.
Definition LAY_XT : layout_t := [(24, 8%N); (80, 8%N)].
Definition XT_RET : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1634).
Definition ss_XT : sstate :=
mkSS PC_XT sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 (obj_chunks_from LAY_XT 32) ] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_XTr : sstate :=
mkSS XT_RET sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 (obj_chunks_from LAY_XT 32) ] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XT_at : forall regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t,
K_XD (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XT (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t KXD HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & G24 & G20 & G21 & G8 & S80 & S24 & S48 & Hobj & Hcg & Hchq & Htree & Hth & Hpnew & Hfimg & Hfdp & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HCSv : CHT_SIZE = 48) by reflexivity.
assert (HFTv : FREETREE_STK = 12304) by reflexivity.
set (keep := (keep2 pnew fimg ++ cht_blks C) ++ [(fdp, fdn)]).
assert (HB' : Permutation (blocks Lc Ac) (keep ++ tree_blocks t)).
{ eapply Permutation_trans; [exact HB|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
assert (HBt : Permutation (blocks Lc Ac) (tree_blocks t ++ keep)) by (eapply Permutation_trans; [exact HB' | apply Permutation_app_comm]).
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 keep)
by (intros x0 Hx0; subst keep; apply in_app_iff; left; apply in_app_iff; left; apply in_app_iff; left; exact Hx0).
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
assert (Hpin : In (pnew, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB'|]. apply in_app_iff; left. subst keep.
apply in_app_iff; left. apply in_app_iff; left. apply in_app_iff; right. left. reflexivity. }
destruct (heap_blocks_range _ _ LAWS _ _ _ _ _ _ HHc Hpin ltac:(destruct Hfmt as [-> | ->]; lia)) as (Rp0 & Rp1 & _).
assert (Rtr : 0 <= troot t < 2 ^ 64).
{ destruct t as [|n|n l r1]; cbn [troot]; [lia | |];
(assert (Hin : In (tn_addr n, NODE_SIZE) (blocks Lc Ac))
by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; right; cbn [tree_blocks]; left; reflexivity]);
destruct (heap_blocks_range _ _ LAWS _ _ _ _ _ _ HHc Hin ltac:(unfold NODE_SIZE; lia)) as (Ha0 & Ha1 & _); unfold NODE_SIZE in *; lia). }
assert (HoXT : obj_at ubs2segs memc (sp regs0) LAY_XT [pnew; troot t]).
{ cbn [obj_at LAY_XT].
split; [split; [cbn [fst snd]; apply val_mem_word_mem; exact S24 | cbn [fst snd]; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia]|].
split; [split; [cbn [fst snd]; apply val_mem_word_mem; exact S80 | cbn [fst snd]; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia]|]. exact I. }
set (E := Ereg regs1 (map (Z_to_bv 64) [pnew; troot t] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE33 : ew E 33 = Z_to_bv 64 (troot t)) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) ubs2segs E ss_XT (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT) memc (seg_rom ubs2segs))).
{ unfold ss_XT. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj ubs2segs _ memc 2 (sp regs0)); [exact HU2 | unfold sp, sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HoXT | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs1 _ [] jj v Hjj).
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free_decision_tree. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
jreg HS (10%bv:reg) as Hr10. rewrite HE33 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREETREE_STK) (FP1 := blocks_fp (tree_blocks t))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) keep);
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm in HPRE1 |- *. eapply SR_mono.
{ eapply (FTREE fxi Lc Ac (ms_regs ms) memc mdc t keep HPRE1 Hr10 Htree Hth HBt). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station Lc Ac memc mdc keep (tree_blocks t) b n HHc HB' HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte ubs2segs mem5 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep' : forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte ubs2segs mem5 (b + i) = mbyte ubs2segs memc (b + i)).
{ rewrite <- Hmm. eapply (kept_across_call FREETREE_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L5 A5 mem5 md5 keep (tree_blocks t));
[rewrite Hmm; exact HHc | exact HB' | exact HJc5 | exact HB5]. }
assert (HB5' : Permutation (blocks L5 A5) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, fdn)])).
{ eapply Permutation_trans; [exact HB5|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
assert (Hr2' : getr regs5 2 = Z_to_bv 64 (sp regs0)) by (rewrite (regs_preserved_frame _ _ HP5 2%bv ltac:(vm_compute; reflexivity)); exact Hr2).
assert (HoXT5 : obj_at ubs2segs mem5 (sp regs0) LAY_XT [pnew; troot t]).
{ eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBA_FRAME); [exact HoXT | reflexivity |].
intros i Hi. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
set (E5 := Ereg regs5 (map (Z_to_bv 64) [pnew; troot t] ++ [])).
assert (HE5 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E5 n = getr regs5 rr) by (intros; subst E5; apply ew_Ereg_nat; assumption).
assert (HE5p : ew E5 32 = Z_to_bv 64 pnew) by (subst E5; apply (Ereg_vals regs5 _ [] 0%nat); reflexivity).
assert (HU5 : bv_unsigned (ew E5 2) = sp regs0) by (rewrite (HE5 2%nat 2%bv eq_refl), Hr2'; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
assert (HS5 : st_ok (fx:=fxi) ubs2segs E5 ss_XTr (mkst (fx:=fxi) regs5 (Z_to_bv 64 XT_RET) mem5 (seg_rom ubs2segs))).
{ unfold ss_XTr. subst E5. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj ubs2segs _ mem5 2 (sp regs0)); [exact HU5 | unfold sp, sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HoXT5 | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs5 _ [] jj v Hjj).
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU5.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 XT_RET) end.
change mem5 with (ms_mem (mkst (fx:=fxi) regs5 (Z_to_bv 64 XT_RET) mem5 (seg_rom ubs2segs))) in HJ5. try clear HF HG.
jrun_to LAWS ubs2tbl_ok HS5 HJ5 PC_XD. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ5.
assert (Hmm5 : ms_mem ms0 = mem5) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
clear HF HG.
rewrite (st_ok_mkst ubs2segs _ _ _ HS5 eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XD) end. rewrite Hmm5. rewrite Hmm5 in HJ5.
assert (R5 : forall k : reg, Z.of_nat (Z.to_nat (bv_unsigned k)) = bv_unsigned k -> In k [3; 8; 20; 21; 24]%bv ->
getr (ms_regs ms0) k = getr (ms_regs ms) k).
{ intros k Hk Hin. rewrite (regs_kept_of_st_ok ubs2segs _ _ _ regs5 _ [3; 8; 20; 21; 24]%bv HS5 ltac:(subst E5; apply env_agree_refl) ltac:(vm_compute; reflexivity) k Hin).
apply (regs_preserved_frame _ _ HP5 k). clear - Hin. cbv in Hin. destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]]; vm_compute; reflexivity. }
apply (KXD fxi (ms_regs ms0) L5 A5 mem5 md5 ha pnew fimg C cnt pal fdp fdn HFRM).
split.
{
split; [exact HJ5|].
split; [exact (init_of_live_r L5 A5 mem5 md5 _ (proj1 HJ5) HB5')|].
split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem5 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS5 (2%bv:reg) as Hq; rewrite Hq; exact (eq_trans (HE5 2%nat 2%bv eq_refl) Hr2')|].
split; [rewrite (R5 3%bv eq_refl ltac:(cbv; tauto)); jreg HS (3%bv:reg) as Hq3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hq3; exact Hq3|].
jreg HS5 (4%bv:reg) as Hq; rewrite Hq, (HE5 4%nat 4%bv eq_refl), (regs_preserved_frame _ _ HP5 4%bv ltac:(vm_compute; reflexivity)), Hr4, Htp0. reflexivity. }
split; [exact Hfmt|].
split. { rewrite (R5 24%bv eq_refl ltac:(cbv; tauto)). jreg HS (24%bv:reg) as Hq. rewrite (HE 24%nat 24%bv eq_refl), G24 in Hq. exact Hq. }
split. { jreg HS5 (18%bv:reg) as Hq. rewrite Hq. exact HE5p. }
split. { rewrite (R5 20%bv eq_refl ltac:(cbv; tauto)). jreg HS (20%bv:reg) as Hq. rewrite (HE 20%nat 20%bv eq_refl), G20 in Hq. exact Hq. }
split. { rewrite (R5 21%bv eq_refl ltac:(cbv; tauto)). jreg HS (21%bv:reg) as Hq. rewrite (HE 21%nat 21%bv eq_refl), G21 in Hq. exact Hq. }
split. { rewrite (R5 8%bv eq_refl ltac:(cbv; tauto)). jreg HS (8%bv:reg) as Hq. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hq. exact Hq. }
split. { eapply slot_kept; [exact S48 | unfold SL_fimg; lia | unfold sp, sp0, RGBA_FRAME in *; lia | unfold SL_fimg, sp, sp0, RGBA_FRAME in *; lia | exact HI]. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i); [apply Hsub; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N keep); [| exact Hcg | exact Hkeep'].
subst keep. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { eapply chtq_ok_kept; [exact Hchq | |].
- intros i Hi. apply (Hkeep' (ch_c C) CHT_SIZE i); [subst keep; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity | exact Hi].
- intros i Hi. apply (Hkeep' (ch_p C) (3 * ch_T C) i); [subst keep; apply in_app_iff; left; apply in_app_iff; right; right; right; right; right; left; reflexivity | exact Hi]. }
split; [exact Hpnew|]. split; [exact Hfimg|]. split; [exact Hfdp|]. exact HB5'.
Qed.
Definition LAY_XT2 : layout_t := [(24, 8%N)].
Definition XT2_RET : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x140c).
Definition ss_XT2 : sstate := mkSS PC_XT2 sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_XT2r : sstate :=
mkSS XT2_RET sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 (obj_chunks_from LAY_XT2 32) ] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XT2_at : forall regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t,
K_XC (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XT2 (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT2) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t KXC HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & G19 & G20 & G21 & G8 & S24 & S48 & Hobj & Hcg & Hchq & Htree & Hth & Hpnew & Hfimg & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HCSv : CHT_SIZE = 48) by reflexivity.
assert (HFTv : FREETREE_STK = 12304) by reflexivity.
set (keep := keep2 pnew fimg ++ cht_blks C).
assert (HB' : Permutation (blocks Lc Ac) (keep ++ tree_blocks t)).
{ eapply Permutation_trans; [exact HB|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
assert (HBt : Permutation (blocks Lc Ac) (tree_blocks t ++ keep)) by (eapply Permutation_trans; [exact HB' | apply Permutation_app_comm]).
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 keep)
by (intros x0 Hx0; subst keep; apply in_app_iff; left; apply in_app_iff; left; exact Hx0).
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
assert (Hpin : In (pnew, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB'|]. apply in_app_iff; left. subst keep.
apply in_app_iff; left. apply in_app_iff; right. left. reflexivity. }
destruct (heap_blocks_range _ _ LAWS _ _ _ _ _ _ HHc Hpin ltac:(destruct Hfmt as [-> | ->]; lia)) as (Rp0 & Rp1 & _).
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) ubs2segs E ss_XT2 (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT2) memc (seg_rom ubs2segs))).
{ unfold ss_XT2. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XT2) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free_decision_tree. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Hr10. rewrite (HE 19%nat 19%bv eq_refl), G19 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREETREE_STK) (FP1 := blocks_fp (tree_blocks t))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) keep);
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm in HPRE1 |- *. eapply SR_mono.
{ eapply (FTREE fxi Lc Ac (ms_regs ms) memc mdc t keep HPRE1 Hr10 Htree Hth HBt). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station Lc Ac memc mdc keep (tree_blocks t) b n HHc HB' HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte ubs2segs mem5 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep' : forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte ubs2segs mem5 (b + i) = mbyte ubs2segs memc (b + i)).
{ rewrite <- Hmm. eapply (kept_across_call FREETREE_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L5 A5 mem5 md5 keep (tree_blocks t));
[rewrite Hmm; exact HHc | exact HB' | exact HJc5 | exact HB5]. }
assert (HB5' : Permutation (blocks L5 A5) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C)).
{ eapply Permutation_trans; [exact HB5|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
assert (Hr2' : getr regs5 2 = Z_to_bv 64 (sp regs0)) by (rewrite (regs_preserved_frame _ _ HP5 2%bv ltac:(vm_compute; reflexivity)); exact Hr2).
assert (HoXT2 : obj_at ubs2segs mem5 (sp regs0) LAY_XT2 [pnew]).
{ cbn [obj_at LAY_XT2]. split; [|exact I]. split; [|cbn [fst snd]; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia].
cbn [fst snd]. apply val_mem_word_mem.
eapply slot_kept; [exact S24 | unfold SL_new; lia | unfold sp, sp0, RGBA_FRAME in *; lia | unfold SL_new, sp, sp0, RGBA_FRAME in *; lia | exact HI]. }
set (E5 := Ereg regs5 (map (Z_to_bv 64) [pnew] ++ [])).
assert (HE5 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E5 n = getr regs5 rr) by (intros; subst E5; apply ew_Ereg_nat; assumption).
assert (HE5p : ew E5 32 = Z_to_bv 64 pnew) by (subst E5; apply (Ereg_vals regs5 _ [] 0%nat); reflexivity).
assert (HU5 : bv_unsigned (ew E5 2) = sp regs0) by (rewrite (HE5 2%nat 2%bv eq_refl), Hr2'; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
assert (HS5 : st_ok (fx:=fxi) ubs2segs E5 ss_XT2r (mkst (fx:=fxi) regs5 (Z_to_bv 64 XT2_RET) mem5 (seg_rom ubs2segs))).
{ unfold ss_XT2r. subst E5. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj ubs2segs _ mem5 2 (sp regs0)); [exact HU5 | unfold sp, sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HoXT2 | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs5 _ [] jj v Hjj).
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU5.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 XT2_RET) end.
change mem5 with (ms_mem (mkst (fx:=fxi) regs5 (Z_to_bv 64 XT2_RET) mem5 (seg_rom ubs2segs))) in HJ5. try clear HF HG.
jrun_to LAWS ubs2tbl_ok HS5 HJ5 PC_XC. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ5.
assert (Hmm5 : ms_mem ms0 = mem5) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
clear HF HG.
rewrite (st_ok_mkst ubs2segs _ _ _ HS5 eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XC) end. rewrite Hmm5. rewrite Hmm5 in HJ5.
assert (R5 : forall k : reg, In k [3; 8; 20; 21]%bv -> getr (ms_regs ms0) k = getr (ms_regs ms) k).
{ intros k Hin. rewrite (regs_kept_of_st_ok ubs2segs _ _ _ regs5 _ [3; 8; 20; 21]%bv HS5 ltac:(subst E5; apply env_agree_refl) ltac:(vm_compute; reflexivity) k Hin).
apply (regs_preserved_frame _ _ HP5 k). clear - Hin. cbv in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]]; vm_compute; reflexivity. }
apply (KXC fxi (ms_regs ms0) L5 A5 mem5 md5 ha pnew fimg C cnt pal HFRM).
split.
{
split; [exact HJ5|].
split; [exact (init_of_live_r L5 A5 mem5 md5 _ (proj1 HJ5) HB5')|].
split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem5 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS5 (2%bv:reg) as Hq; rewrite Hq; exact (eq_trans (HE5 2%nat 2%bv eq_refl) Hr2')|].
split; [rewrite (R5 3%bv ltac:(cbv; tauto)); jreg HS (3%bv:reg) as Hq3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hq3; exact Hq3|].
jreg HS5 (4%bv:reg) as Hq; rewrite Hq, (HE5 4%nat 4%bv eq_refl), (regs_preserved_frame _ _ HP5 4%bv ltac:(vm_compute; reflexivity)), Hr4, Htp0. reflexivity. }
split; [exact Hfmt|].
split. { rewrite (R5 20%bv ltac:(cbv; tauto)). jreg HS (20%bv:reg) as Hq. rewrite (HE 20%nat 20%bv eq_refl), G20 in Hq. exact Hq. }
split. { jreg HS5 (18%bv:reg) as Hq. rewrite Hq. exact HE5p. }
split. { rewrite (R5 8%bv ltac:(cbv; tauto)). jreg HS (8%bv:reg) as Hq. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hq. exact Hq. }
split. { rewrite (R5 21%bv ltac:(cbv; tauto)). jreg HS (21%bv:reg) as Hq. rewrite (HE 21%nat 21%bv eq_refl), G21 in Hq. exact Hq. }
split. { eapply slot_kept; [exact S48 | unfold SL_fimg; lia | unfold sp, sp0, RGBA_FRAME in *; lia | unfold SL_fimg, sp, sp0, RGBA_FRAME in *; lia | exact HI]. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (Hkeep' r RGB_SIZE i); [apply Hsub; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N keep); [| exact Hcg | exact Hkeep'].
subst keep. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split. { eapply chtq_ok_kept; [exact Hchq | |].
- intros i Hi. apply (Hkeep' (ch_c C) CHT_SIZE i); [subst keep; apply in_app_iff; right; left; reflexivity | exact Hi].
- intros i Hi. apply (Hkeep' (ch_p C) (3 * ch_T C) i); [subst keep; apply in_app_iff; right; right; right; right; right; left; reflexivity | exact Hi]. }
split; [exact Hpnew|]. split; [exact Hfimg|]. exact HB5'.
Qed.
Definition ss_XC : sstate :=
mkSS PC_XC sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 (obj_chunks_from LAY_XC 32) ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Lemma XC_at : forall regs1 Lc Ac memc mdc ha pnew fimg C cnt pal,
K_XF (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_XC (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg C cnt pal ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XC) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg C cnt pal KXF HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & G20 & G18 & G8 & G21 & S48 & Hobj & Hcg & Hchq & Hpnew & Hfimg & HB).
destruct C as [c f h u p x T hS uS TS Ht ent]. cbn [ch_c ch_f ch_h ch_u ch_p ch_x ch_T ch_hS ch_uS ch_TS ch_H ch_ent] in *.
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HCSv : CHT_SIZE = 48) by reflexivity. assert (HFSv : FREECHT_STK = 8208) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
destruct Hchq as (Hcht & Hpal & Hpl & HTin & Hlow).
set (tmp := cht_blks (mkCHT c f h u p x T hS uS TS Ht ent)) in *.
assert (HL : forall q n, In (q, n) tmp -> q <> 0) by (intros q n Hq; pose proof (Hlow _ Hq) as Hq'; cbn [fst] in Hq'; lia).
pose proof (HL f (4 * T) ltac:(right; left; reflexivity)) as Hf0.
pose proof (HL h (3 * T) ltac:(right; right; left; reflexivity)) as Hh0.
pose proof (HL u T ltac:(right; right; right; left; reflexivity)) as Hu0.
pose proof (HL p (3 * T) ltac:(right; right; right; right; left; reflexivity)) as Hp0.
pose proof (HL x (4 * T) ltac:(right; right; right; right; right; left; reflexivity)) as Hx0.
assert (HB' : Permutation (blocks Lc Ac) (keep2 pnew fimg ++ tmp)).
{ eapply Permutation_trans; [exact HB|]. rewrite app_assoc. apply Permutation_refl. }
assert (HBc : Permutation (blocks Lc Ac) ((c, CHT_SIZE) :: optb f (4 * T) ++ optb h (3 * T) ++ optb u T ++ optb p (3 * T) ++ optb x (4 * T) ++ keep2 pnew fimg)).
{ rewrite (optb_nz f _ Hf0), (optb_nz h _ Hh0), (optb_nz u _ Hu0), (optb_nz p _ Hp0), (optb_nz x _ Hx0).
eapply Permutation_trans; [exact HB'|]. apply Permutation_app_comm. }
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 (keep2 pnew fimg)) by (intros x0 Hx'; apply in_app_iff; left; exact Hx').
assert (Hpin : In (pnew, fmt * N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; left; apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc pnew (fmt * N) HHc Hpin ltac:(clear - Hfmt HN1; nia)) as (Hp0' & Hp1' & _).
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; left; apply in_app_iff; left; left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc Hrin ltac:(lia)) as (Rr0 & Rr1 & _).
assert (Hcin : In (c, CHT_SIZE) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc c CHT_SIZE HHc Hcin ltac:(lia)) as (Hc0 & Hc1 & _).
assert (Hfin : In (fimg, N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB' | apply in_app_iff; left; apply in_app_iff; right; right; left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc fimg N HHc Hfin ltac:(lia)) as (Hf0' & Hf1' & _).
assert (HoXC : obj_at ubs2segs memc (sp regs0) LAY_XC [fimg]).
{ cbn [obj_at LAY_XC].
split; [split; [cbn [fst snd]; apply val_mem_word_mem; exact S48 | cbn [fst snd]; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia]|]. exact I. }
set (E := Ereg regs1 (map (Z_to_bv 64) [fimg] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp regs0) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : sp regs0 mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok (fx:=fxi) ubs2segs E ss_XC (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XC) memc (seg_rom ubs2segs))).
{ unfold ss_XC. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj ubs2segs _ memc 2 (sp regs0)); [exact HU2 | unfold sp, sp0 in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | exact HoXC | reflexivity | | intros i Hi; lia].
intros jj v Hjj. apply (Ereg_vals regs1 _ [] jj v Hjj).
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_XC) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free_col_hash_table. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
clear HF HG.
jreg HS (10%bv:reg) as Hr10. rewrite (HE 20%nat 20%bv eq_refl), G20 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms) = sp regs0) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECHT_STK)
(FP1 := (c, c + CHT_SIZE) :: optfp f (4 * T) ++ optfp h (3 * T) ++ optfp u T ++ optfp p (3 * T) ++ optfp x (4 * T))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) (keep2 pnew fimg));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Hmm in HPRE1 |- *. eapply SR_mono.
{ eapply (FCHT fxi Lc Ac (ms_regs ms) memc mdc c f h u p x cnt T (4 * T) (3 * T) T (3 * T) (4 * T) (keep2 pnew fimg) HPRE1 Hr10 Hcht HBc). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right.
assert (Ha' : inFP (blocks_fp tmp) a).
{ subst tmp. cbn [cht_blks cht_blocks ch_c ch_f ch_h ch_u ch_p ch_x ch_T blocks_fp map fst snd].
unfold optfp in Ha. rewrite (proj2 (Z.eqb_neq f 0) Hf0), (proj2 (Z.eqb_neq h 0) Hh0), (proj2 (Z.eqb_neq u 0) Hu0), (proj2 (Z.eqb_neq p 0) Hp0), (proj2 (Z.eqb_neq x 0) Hx0) in Ha.
cbn [app] in Ha. exact Ha. }
apply inFP_blocks_fp in Ha' as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station Lc Ac memc mdc (keep2 pnew fimg) tmp b n HHc HB' HBent Hsub Hbn ltac:(lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (HH5 & _ & Hhi5 & _).
assert (HI5 : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte ubs2segs mem5 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- Hmm. apply (proj1 (Hhi5 x0 Hx ltac:(rewrite Hspms; lia))). }
assert (Hkeep5 : forall b m i, In (b, m) (keep2 pnew fimg) -> 0 <= i < m -> mbyte ubs2segs mem5 (b + i) = mbyte ubs2segs memc (b + i)).
{ rewrite <- Hmm. eapply (kept_across_call FREECHT_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L5 A5 mem5 md5 (keep2 pnew fimg) tmp);
[rewrite Hmm; exact HHc | exact HB' | | exact HB5].
subst tmp. cbn [cht_blks cht_blocks ch_c ch_f ch_h ch_u ch_p ch_x ch_T blocks_fp map fst snd].
unfold optfp in HJc5. rewrite (proj2 (Z.eqb_neq f 0) Hf0), (proj2 (Z.eqb_neq h 0) Hh0), (proj2 (Z.eqb_neq u 0) Hu0), (proj2 (Z.eqb_neq p 0) Hp0), (proj2 (Z.eqb_neq x 0) Hx0) in HJc5.
cbn [app] in HJc5. exact HJc5. }
jafter_call_keep HS 33%nat regs5 mem5 HP5 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi5 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | rewrite Hspms; lia | cbn; lia | cbn; lia]. }
clear HS Hr10 Hr2 Hr4 Hr1. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ5 ubs2_A_free. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_regs ms_mem mkst] in HF, HJ5.
assert (Hmm1 : ms_mem ms0 = mem5) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
clear HF HG.
jreg HS (10%bv:reg) as Hq10. rewrite (HE 18%nat 18%bv eq_refl), G18 in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hq2.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hq4.
jreg HS (1%bv:reg) as Hq1.
assert (HB5c : Permutation (blocks L5 A5) ((pnew, fmt * N) :: BASE r g N img fmt rest s bef beffmt ++ [(fimg, N)])).
{ eapply Permutation_trans; [exact HB5|]. apply Permutation_sym. apply Permutation_middle. }
assert (Hpin5 : In (pnew, fmt * N) (blocks L5 A5)) by (eapply blocks_perm_in; [exact HB5c | left; reflexivity]).
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS ubs2_errno_low IMG (aa_free API)) with (a := pnew) (n := fmt * N) (spc := sp regs0);
[ exact HS | reflexivity | reflexivity | exact HJ5 | exact Hpin5 | exact Hq10 | exact Hq2
| unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| exact Hq4 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin0 i Hi. exfalso.
exact (proj2 (tmp_of_station L5 A5 (ms_mem ms0) md5 (BASE r g N img fmt rest s bef beffmt) [(pnew, fmt * N); (fimg, N)] pnew (fmt * N)
(proj1 HJ5) HB5 HBent ltac:(intros x1 Hx1; exact Hx1) ltac:(left; reflexivity) ltac:(lia)) Hin0). }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hrm6 & Hkeep6 & Hhi6 & Hinit6).
pose proof (perm_after_rm1 _ _ _ _ HB5c Hrm6) as HB6.
jafter_call_keep HS 66%nat regs6 mem6 HP6 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi6 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | lia | cbn; lia | cbn; lia]. }
clear HS Hq10 Hq2 Hq4 Hq1. rename HS2 into HS.
rewrite Hmm1 in Hkeep6, Hhi6.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem6 with (ms_mem msx) in HJ6 end.
jrun_to LAWS ubs2tbl_ok HS HJ6 PC_XF. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ6.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (Hmm6 : ms_mem msx = mem6) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity) end.
clear HF HG.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XF) end. rewrite Hmm6. rewrite Hmm6 in HJ6.
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte ubs2segs mem6 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hsx. rewrite <- (HI5 x0 Hx Hsx). apply (proj1 (Hhi6 x0 Hx ltac:(lia))). }
assert (KB : forall b m i, In (b, m) (BASE r g N img fmt rest s bef beffmt ++ [(fimg, N)]) -> 0 <= i < m ->
mbyte ubs2segs mem6 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (Hkeep5 b m i); [| | exact Hi].
- apply (Hkeep6 b m i); [| exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB6 | exact Hbm].
- apply in_app_iff in Hbm as [Hbm|Hbm]; apply in_app_iff; [left; exact Hbm | right]. right. exact Hbm. }
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ _ _) _) _ => apply (KXF fxi rg L6 A6 mem6 md6 2 fimg N s bef beffmt cur HFRM) end.
split.
{
split; [exact HJ6|]. split; [exact Hinit6|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem6 (sp regs0)); [exact HRA | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp0 in *; lia | unfold sp0 in *; lia | exact HI]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply HI; unfold sp, sp0, RGBA_FRAME in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [lia|].
split; [jreg HS (9%bv:reg) as Hq; rewrite Hq; exact HE32|].
split; [jreg HS (21%bv:reg) as Hq; rewrite Hq, (HE 21%nat 21%bv eq_refl); exact G21|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (KB r RGB_SIZE i); [apply in_app_iff; left; left; reflexivity | exact Hi]. }
split. { eapply (cgif_at_kept _ _ g s N (BASE r g N img fmt rest s bef beffmt ++ [(fimg, N)])); [| exact Hcg | exact KB].
unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbef|].
split; [exact Hfimg|].
split. { exact (proj2 (tmp_of_station L6 A6 mem6 md6 (BASE r g N img fmt rest s bef beffmt) [(fimg, N)] fimg N
(proj1 HJ6) HB6 HBent ltac:(intros x1 Hx1; exact Hx1) ltac:(left; reflexivity) ltac:(lia))). }
exact HB6.
Qed.
End j.
Lemma ubs2_rgbadd_XD : seg_XD API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXC fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn HFRM HAT. exact (XD_at regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn KXC HFRM HAT). Qed.
Lemma ubs2_rgbadd_XT : seg_XT API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXD fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t HFRM HAT. exact (XT_at regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t KXD HFRM HAT). Qed.
Lemma ubs2_rgbadd_XT2 : seg_XT2 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXC fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t HFRM HAT. exact (XT2_at regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t KXC HFRM HAT). Qed.
Lemma ubs2_rgbadd_XC : seg_XC API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KXF fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal HFRM HAT. exact (XC_at regs1 Lc Ac memc mdc ha pnew fimg C cnt pal KXF HFRM HAT). Qed.
End e.
End d.
