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
UI1e UI1i UI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g UI3h UI3d
UI4v UI46 UI4g.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Local Notation AT_R2 := (at_R2 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_M3 := (at_M3 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_M4 := (at_M4 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_M5 := (at_M5 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_FAIL := (at_FAIL API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_C0 := (at_C0 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation KEEPB := (keepb r g bef beffmt s N img fmt rest).
Local Notation RZ_MEM_KEPT := (rz_mem_kept API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation RINV := (rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation RZ_MEM_ZSUM := (rz_mem_zsum regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_HT := (rz_mem_ht regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RINV_MEM := (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation RINV_CALL := (rgba_inv_call API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Section S3.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc p1 x1 h1, AT_M3 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M3) memc (seg_rom ubs2segs)) mdc) POST.
Theorem R2_stretch : forall regs1 Lc Ac memc mdc p1 x1, AT_R2 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_R2) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 HAT.
destruct HAT as (HINV & (Hfmt & Hi & Hha & ET') & (HREGS & G9 & G20 & G8 & G21) & G10 & G27 & G26 & G24 & G19 & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
set (T := ch_T C) in *.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E (mkSS PC_R2 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_R2) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_R2) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jreg HS (10%bv:reg) as Ma0. rewrite (HE 24%nat 24%bv eq_refl), G24 in Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 27; 26; 19]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := 3 * T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact Ma0 | lia
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hinit2 & HP2 & Hr10 & Hres & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hres, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
destruct (malloc_post_perm _ _ _ res (3 * T') _ RZB Hres) as [HB2 Hsub2].
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b n k, In (b, n) (KEEPB pnew fimg C) -> 0 <= k < n -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b n k Hb Hk. apply (Hkeep2 b n k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact RZB|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 80676) with (Z_to_bv 64 PC_M3). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1 res). unfold at_M3.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [split; [exact Hfmt|]; split; [exact Hi|]; split; [exact Hha | exact ET']|].
split. { unfold rz_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split; [exact Hr10|].
split; [rewrite RP by (vm_compute; reflexivity); jreg HS (22%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 27%bv ltac:(cbv; auto 20)); exact G27|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 26%bv ltac:(cbv; auto 20)); exact G26|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 19%bv ltac:(cbv; auto 20)); exact G19|].
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| intros b n k Hb Hk; exact (KB2 b n k (keepb_sub r g bef beffmt s N img fmt rest _ _ _ _ Hb) Hk) | exact Hz].
intros a Ha Hs _ _. apply KH2; [exact Ha | exact Hs]. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KH2; unfold sp, sp0 in *; lia. }
split. { exact (rz_struct_kept r g bef beffmt s N img fmt rest memc mem2 pnew fimg C _ _ _ RZS KB2). }
unfold rz_blocks. eapply Permutation_trans; [exact HB2|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.
End S3.
Section S4.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc p1 x1 h1 u1, AT_M4 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M4) memc (seg_rom ubs2segs)) mdc) POST.
Theorem M3_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1, AT_M3 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M3) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 HAT.
destruct HAT as (HINV & (Hfmt & Hi & Hha & ET') & (HREGS & G9 & G20 & G8 & G21) & G10 & G22 & G27 & G26 & G19 & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
set (T := ch_T C) in *.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E (mkSS PC_M3 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_M3) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_M3) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jreg HS (10%bv:reg) as Ma0. rewrite (HE 19%nat 19%bv eq_refl), G19 in Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 22; 27; 26; 19]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact Ma0 | lia
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hinit2 & HP2 & Hr10 & Hres & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hres, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
destruct (malloc_post_perm _ _ _ res (T') _ RZB Hres) as [HB2 Hsub2].
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b n k, In (b, n) (KEEPB pnew fimg C) -> 0 <= k < n -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b n k Hb Hk. apply (Hkeep2 b n k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact RZB|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 80688) with (Z_to_bv 64 PC_M4). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1 h1 res). unfold at_M4.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [split; [exact Hfmt|]; split; [exact Hi|]; split; [exact Hha | exact ET']|].
split. { unfold rz_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split; [exact Hr10|].
split; [rewrite RP by (vm_compute; reflexivity); jreg HS (24%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 22%bv ltac:(cbv; auto 20)); exact G22|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 27%bv ltac:(cbv; auto 20)); exact G27|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 26%bv ltac:(cbv; auto 20)); exact G26|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 19%bv ltac:(cbv; auto 20)); exact G19|].
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| intros b n k Hb Hk; exact (KB2 b n k (keepb_sub r g bef beffmt s N img fmt rest _ _ _ _ Hb) Hk) | exact Hz].
intros a Ha Hs _ _. apply KH2; [exact Ha | exact Hs]. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KH2; unfold sp, sp0 in *; lia. }
split. { exact (rz_struct_kept r g bef beffmt s N img fmt rest memc mem2 pnew fimg C _ _ _ RZS KB2). }
unfold rz_blocks. eapply Permutation_trans; [exact HB2|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.
End S4.
Section S5.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_M5 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M5) memc (seg_rom ubs2segs)) mdc) POST.
Theorem M4_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1 u1, AT_M4 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M4) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 u1 HAT.
destruct HAT as (HINV & (Hfmt & Hi & Hha & ET') & (HREGS & G9 & G20 & G8 & G21) & G10 & G24 & G22 & G27 & G26 & G19 & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
set (T := ch_T C) in *.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E (mkSS PC_M4 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_M4) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_M4) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jreg HS (10%bv:reg) as Ma0. rewrite (HE 26%nat 26%bv eq_refl), G26 in Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 24; 22; 27; 19]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := 4 * T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact Ma0 | lia
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hinit2 & HP2 & Hr10 & Hres & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hres, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
destruct (malloc_post_perm _ _ _ res (4 * T') _ RZB Hres) as [HB2 Hsub2].
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b n k, In (b, n) (KEEPB pnew fimg C) -> 0 <= k < n -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b n k Hb Hk. apply (Hkeep2 b n k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact RZB|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 80700) with (Z_to_bv 64 PC_M5). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1 h1 u1 res). unfold at_M5.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [split; [exact Hfmt|]; split; [exact Hi|]; split; [exact Hha | exact ET']|].
split. { unfold rz_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split; [exact Hr10|].
split; [rewrite RP by (vm_compute; reflexivity); jreg HS (25%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 24%bv ltac:(cbv; auto 20)); exact G24|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 22%bv ltac:(cbv; auto 20)); exact G22|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 27%bv ltac:(cbv; auto 20)); exact G27|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 19%bv ltac:(cbv; auto 20)); exact G19|].
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| intros b n k Hb Hk; exact (KB2 b n k (keepb_sub r g bef beffmt s N img fmt rest _ _ _ _ Hb) Hk) | exact Hz].
intros a Ha Hs _ _. apply KH2; [exact Ha | exact Hs]. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KH2; unfold sp, sp0 in *; lia. }
split. { exact (rz_struct_kept r g bef beffmt s N img fmt rest memc mem2 pnew fimg C _ _ _ RZS KB2). }
unfold rz_blocks. eapply Permutation_trans; [exact HB2|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.
End S5.
Section S6.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KFAIL : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_FAIL regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_FAIL) memc (seg_rom ubs2segs)) mdc) POST.
Hypothesis KC0 : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_C0 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_C0) memc (seg_rom ubs2segs)) mdc) POST.
Theorem M5_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_M5 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M5) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 u1 f1 HAT.
destruct HAT as (HINV & HRZF & (HREGS & G9 & G20 & G8 & G21) & G10 & G25 & G24 & G22 & G27 & G19 & RZM & S72 & RZS & RZB).
destruct HREGS as (G2 & G3 & G4). pose proof (proj1 HINV) as HJ.
pose proof HINV as (_ & _ & _ & _ & Hal0 & _).
pose proof (proj1 HJ) as HHc. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T' ++ optb f1 (4 * T')) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact RZB |]. exact Hb. }
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 0 <= q < 2 ^ 64).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (R0 & R1 & _). lia. }
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt).
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). pose proof HRZF as (Hfmt & _ & _ & ET').
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & _ & (RT1' & _)). rewrite <- ET' in Hch', RT1'.
pose proof RZS as Hobjc. unfold rz_struct in Hobjc.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 3 _ _ Hobjc eq_refl eq_refl) as [_ Rp]. pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 4 _ _ Hobjc eq_refl eq_refl) as [_ Rx].
cbn [fst snd] in Rp, Rx. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rp, Rx.
assert (Rp1 : 0 <= p1 < 2 ^ 64).
{ unfold rbk in INB. destruct (Z.eqb_spec p1 0) as [->|Hnz]; [lia|]. apply (RNG p1 (3 * T')); [| lia]. apply INB. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
assert (Rx1 : 0 <= x1 < 2 ^ 64).
{ unfold rbk in INB. destruct (Z.eqb_spec x1 0) as [->|Hnz]; [lia|]. apply (RNG x1 (4 * T')); [| lia]. apply INB. apply in_app_iff. right. apply in_app_iff. left. right. left. destruct (p1 =? 0); reflexivity. }
assert (Rh1 : 0 <= h1 < 2 ^ 64).
{ unfold optb in INB. destruct (Z.eqb_spec h1 0) as [->|Hnz]; [lia|]. apply (RNG h1 (3 * T')); [| lia]. apply INB. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
assert (Ru1 : 0 <= u1 < 2 ^ 64).
{ unfold optb in INB. destruct (Z.eqb_spec u1 0) as [->|Hnz]; [lia|]. apply (RNG u1 T'); [| lia]. apply INB. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
assert (Rf1 : 0 <= f1 < 2 ^ 64).
{ unfold optb in INB. destruct (Z.eqb_spec f1 0) as [->|Hnz]; [lia|]. apply (RNG f1 (4 * T')); [| lia]. apply INB. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE27 : ew E 27 = Z_to_bv 64 p1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE22 : ew E 22 = Z_to_bv 64 x1) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE24 : ew E 24 = Z_to_bv 64 h1) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE25 : ew E 25 = Z_to_bv 64 u1) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HE10 : ew E 10 = Z_to_bv 64 f1) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E (mkSS PC_M5 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_M5) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_M5) memc (seg_rom ubs2segs))) in HJ. clearbody E.
assert (ARRF : forall ss ms', st_ok ubs2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_FAIL ->
ms_mem ms' = memc -> getr (ms_regs ms') 26 = Z_to_bv 64 f1 ->
(p1 = 0 \/ x1 = 0 \/ h1 = 0 \/ u1 = 0 \/ f1 = 0) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 9; 20; 8; 21; 27; 22; 24; 25; 19]%bv = true ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hrv Hpc Em' M26 Hz0 QK.
pose proof (regs_kept_of_st_ok ubs2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc, Em'. apply (KFAIL (ms_regs ms') Lc Ac memc mdc p1 x1 h1 u1 f1). unfold at_FAIL.
split; [exact HINV|]. split; [exact HRZF|].
split. { unfold rz_regs, rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split. { unfold chk_regs.
rewrite (GK 27%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)), (GK 19%bv ltac:(cbv; auto 20)).
repeat (split; [assumption|]). exact G19. }
split; [exact Hz0|]. split; [exact RZM|]. split; [exact S72|]. split; [exact RZS | exact RZB]. }
assert (ARRC : forall ss ms', st_ok ubs2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_C0 ->
ms_mem ms' = memc -> getr (ms_regs ms') 26 = Z_to_bv 64 f1 ->
p1 <> 0 -> x1 <> 0 -> h1 <> 0 -> u1 <> 0 -> f1 <> 0 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 9; 20; 8; 21; 27; 22; 24; 25; 19]%bv = true ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hrv Hpc Em' M26 N1 N2 N3 N4 N5 QK.
pose proof (regs_kept_of_st_ok ubs2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc, Em'. apply (KC0 (ms_regs ms') Lc Ac memc mdc p1 x1 h1 u1 f1). unfold at_C0.
split; [exact HINV|]. split; [exact HRZF|].
split. { unfold rz_regs, rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split. { unfold chk_regs.
rewrite (GK 27%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)), (GK 19%bv ltac:(cbv; auto 20)).
repeat (split; [assumption|]). exact G19. }
split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|].
split; [exact RZM|]. split; [exact S72|]. split; [exact RZS|].
unfold rz_blocks. eapply Permutation_trans; [exact RZB|]. unfold rbk, optb.
destruct (Z.eqb_spec p1 0); [lia|]. destruct (Z.eqb_spec x1 0); [lia|]. destruct (Z.eqb_spec h1 0); [lia|]. destruct (Z.eqb_spec u1 0); [lia|]. destruct (Z.eqb_spec f1 0); [lia|].
cbn [app]. apply Permutation_refl. }
Ltac m26 HS HE10 Rf1 := eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; apply (U_atom _ 10 _ HE10); exact Rf1.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K0 : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jbranch ubs2tbl HS.
{ rewrite branch_eq_U, (U_atom E 27 p1 HE27), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PC_FAIL. { apply wr_ok_nil. }
assert (K1 : ms_mem ms0 = memc) by (rewrite <- K0; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF0)).
apply (ARRF _ _ HS eq_refl eq_refl K1); [m26 HS HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 27 p1 HE27), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_nil. }
assert (K1 : ms_mem ms0 = memc) by (rewrite <- K0; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF0)).
jbranch ubs2tbl HS.
{ rewrite branch_eq_U, (U_atom E 22 x1 HE22), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
jrun_to LAWS ubs2tbl_ok HS HJ PC_FAIL. { apply wr_ok_nil. }
assert (K2 : ms_mem ms1 = memc) by (rewrite <- K1; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF1)).
apply (ARRF _ _ HS eq_refl eq_refl K2); [m26 HS HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 22 x1 HE22), U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_nil. }
assert (K2 : ms_mem ms1 = memc) by (rewrite <- K1; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF1)).
jbranch ubs2tbl HS.
{ rewrite branch_eq_U, (U_atom E 24 h1 HE24), U_lit in Hc1 by lia. apply Z.eqb_eq in Hc1.
jrun_to LAWS ubs2tbl_ok HS HJ PC_FAIL. { apply wr_ok_nil. }
assert (K3 : ms_mem ms2 = memc) by (rewrite <- K2; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF2)).
apply (ARRF _ _ HS eq_refl eq_refl K3); [m26 HS HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 24 h1 HE24), U_lit in Hc1 by lia. apply Z.eqb_neq in Hc1.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_nil. }
assert (K3 : ms_mem ms2 = memc) by (rewrite <- K2; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF2)).
jbranch ubs2tbl HS.
{ rewrite branch_eq_U, (U_atom E 25 u1 HE25), U_lit in Hc2 by lia. apply Z.eqb_eq in Hc2.
jrun_to LAWS ubs2tbl_ok HS HJ PC_FAIL. { apply wr_ok_nil. }
assert (K4 : ms_mem ms3 = memc) by (rewrite <- K3; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF3)).
apply (ARRF _ _ HS eq_refl eq_refl K4); [m26 HS HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 25 u1 HE25), U_lit in Hc2 by lia. apply Z.eqb_neq in Hc2.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_nil. }
assert (K4 : ms_mem ms3 = memc) by (rewrite <- K3; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF3)).
jbranch ubs2tbl HS.
{ rewrite branch_eq_U, (U_atom E 10 f1 HE10), U_lit in Hc3 by lia. apply Z.eqb_eq in Hc3.
jrun_to LAWS ubs2tbl_ok HS HJ PC_FAIL. { apply wr_ok_nil. }
assert (K5 : ms_mem ms4 = memc) by (rewrite <- K4; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF4)).
apply (ARRF _ _ HS eq_refl eq_refl K5); [m26 HS HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 10 f1 HE10), U_lit in Hc3 by lia. apply Z.eqb_neq in Hc3.
jrun_to LAWS ubs2tbl_ok HS HJ PC_C0. { apply wr_ok_nil. }
assert (K5 : ms_mem ms4 = memc) by (rewrite <- K4; apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF4)).
apply (ARRC _ _ HS eq_refl eq_refl K5); [m26 HS HE10 Rf1 | exact Hc | exact Hc0 | exact Hc1 | exact Hc2 | exact Hc3 | vm_compute; reflexivity].
Qed.
End S6.
End d.
End c.
