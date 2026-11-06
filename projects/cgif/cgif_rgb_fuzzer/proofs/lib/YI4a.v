(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g YI3h YI3d
YI4v YI46 YI4g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
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
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M3) memc (seg_rom src2segs)) mdc) POST.
Theorem R2_stretch : forall regs1 Lc Ac memc mdc p1 x1, AT_R2 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_R2) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 HAT.
destruct HAT as (HINV & (Hfmt & Hi & Hha & ET') & (HREGS & G9 & G20 & G8 & G21 & G22) & G10 & G26 & G25 & G23 & G18 & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
set (T := ch_T C) in *.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E (mkSS PC_R2 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_R2) memc (seg_rom src2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_R2) memc (seg_rom src2segs))) in HJ. clearbody E.
jrun_to LAWS src2tbl_ok HS HJ src2_A_malloc. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jreg HS (10%bv:reg) as Ma0. rewrite (HE 23%nat 23%bv eq_refl), G23 in Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 22; 26; 25; 18]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS src2_errno_low IMG (aa_malloc API)) with (n := 3 * T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact Ma0 | lia
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hinit2 & HP2 & Hr10 & Hres & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hres, Hkeep2, Hhi2, HJ2.
change (ms_segs src2_msyms) with src2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
destruct (malloc_post_perm _ _ _ res (3 * T') _ RZB Hres) as [HB2 Hsub2].
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte src2segs mem2 a = mbyte src2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b n k, In (b, n) (KEEPB pnew fimg C) -> 0 <= k < n -> mbyte src2segs mem2 (b + k) = mbyte src2segs memc (b + k)).
{ intros b n k Hb Hk. apply (Hkeep2 b n k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact RZB|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 80148) with (Z_to_bv 64 PC_M3). change (ms_segs src2_msyms) with src2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1 res). unfold at_M3.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [split; [exact Hfmt|]; split; [exact Hi|]; split; [exact Hha | exact ET']|].
split. { unfold rz_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G22. }
split; [exact Hr10|].
split; [rewrite RP by (vm_compute; reflexivity); jreg HS (27%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 26%bv ltac:(cbv; auto 20)); exact G26|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 25%bv ltac:(cbv; auto 20)); exact G25|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 18%bv ltac:(cbv; auto 20)); exact G18|].
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
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M4) memc (seg_rom src2segs)) mdc) POST.
Theorem M3_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1, AT_M3 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M3) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 HAT.
destruct HAT as (HINV & (Hfmt & Hi & Hha & ET') & (HREGS & G9 & G20 & G8 & G21 & G22) & G10 & G27 & G26 & G25 & G18 & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
set (T := ch_T C) in *.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E (mkSS PC_M3 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_M3) memc (seg_rom src2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_M3) memc (seg_rom src2segs))) in HJ. clearbody E.
jrun_to LAWS src2tbl_ok HS HJ src2_A_malloc. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jreg HS (10%bv:reg) as Ma0. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 22; 27; 26; 25; 18]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS src2_errno_low IMG (aa_malloc API)) with (n := T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact Ma0 | lia
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hinit2 & HP2 & Hr10 & Hres & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hres, Hkeep2, Hhi2, HJ2.
change (ms_segs src2_msyms) with src2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
destruct (malloc_post_perm _ _ _ res (T') _ RZB Hres) as [HB2 Hsub2].
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte src2segs mem2 a = mbyte src2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b n k, In (b, n) (KEEPB pnew fimg C) -> 0 <= k < n -> mbyte src2segs mem2 (b + k) = mbyte src2segs memc (b + k)).
{ intros b n k Hb Hk. apply (Hkeep2 b n k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact RZB|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 80160) with (Z_to_bv 64 PC_M4). change (ms_segs src2_msyms) with src2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1 h1 res). unfold at_M4.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [split; [exact Hfmt|]; split; [exact Hi|]; split; [exact Hha | exact ET']|].
split. { unfold rz_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G22. }
split; [exact Hr10|].
split; [rewrite RP by (vm_compute; reflexivity); jreg HS (23%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 27%bv ltac:(cbv; auto 20)); exact G27|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 26%bv ltac:(cbv; auto 20)); exact G26|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 25%bv ltac:(cbv; auto 20)); exact G25|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 18%bv ltac:(cbv; auto 20)); exact G18|].
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
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M5) memc (seg_rom src2segs)) mdc) POST.
Theorem M4_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1 u1, AT_M4 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M4) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 u1 HAT.
destruct HAT as (HINV & (Hfmt & Hi & Hha & ET') & (HREGS & G9 & G20 & G8 & G21 & G22) & G10 & G23 & G27 & G26 & G25 & G18 & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
set (T := ch_T C) in *.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E (mkSS PC_M4 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_M4) memc (seg_rom src2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_M4) memc (seg_rom src2segs))) in HJ. clearbody E.
jrun_to LAWS src2tbl_ok HS HJ src2_A_malloc. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jreg HS (10%bv:reg) as Ma0. rewrite (HE 25%nat 25%bv eq_refl), G25 in Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 22; 23; 27; 26; 18]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS src2_errno_low IMG (aa_malloc API)) with (n := 4 * T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact Ma0 | lia
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hinit2 & HP2 & Hr10 & Hres & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hres, Hkeep2, Hhi2, HJ2.
change (ms_segs src2_msyms) with src2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
destruct (malloc_post_perm _ _ _ res (4 * T') _ RZB Hres) as [HB2 Hsub2].
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte src2segs mem2 a = mbyte src2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b n k, In (b, n) (KEEPB pnew fimg C) -> 0 <= k < n -> mbyte src2segs mem2 (b + k) = mbyte src2segs memc (b + k)).
{ intros b n k Hb Hk. apply (Hkeep2 b n k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact RZB|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 80172) with (Z_to_bv 64 PC_M5). change (ms_segs src2_msyms) with src2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1 h1 u1 res). unfold at_M5.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [split; [exact Hfmt|]; split; [exact Hi|]; split; [exact Hha | exact ET']|].
split. { unfold rz_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G22. }
split; [exact Hr10|].
split; [rewrite RP by (vm_compute; reflexivity); jreg HS (24%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 23%bv ltac:(cbv; auto 20)); exact G23|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 27%bv ltac:(cbv; auto 20)); exact G27|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 26%bv ltac:(cbv; auto 20)); exact G26|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 18%bv ltac:(cbv; auto 20)); exact G18|].
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
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_FAIL) memc (seg_rom src2segs)) mdc) POST.
Hypothesis KC0 : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_C0 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_C0) memc (seg_rom src2segs)) mdc) POST.
Theorem M5_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_M5 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_M5) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 u1 f1 HAT.
destruct HAT as (HINV & HRZF & (HREGS & G9 & G20 & G8 & G21 & G22) & G10 & G24 & G23 & G27 & G26 & G18 & RZM & S72 & RZS & RZB).
destruct HREGS as (G2 & G3 & G4). pose proof (proj1 HINV) as HJ.
pose proof HINV as (_ & _ & _ & _ & Hal0 & _).
pose proof (proj1 HJ) as HHc. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T' ++ optb f1 (4 * T')) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact RZB |]. exact Hb. }
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 0 <= q < 2 ^ 64).
{ intros q n Hq Hn. destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (R0 & R1 & _). lia. }
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt).
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). pose proof HRZF as (Hfmt & _ & _ & ET').
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & _ & (RT1' & _)). rewrite <- ET' in Hch', RT1'.
pose proof RZS as Hobjc. unfold rz_struct in Hobjc.
pose proof (obj_at_nth src2segs memc (ch_c C) LAY_Cht _ 3 _ _ Hobjc eq_refl eq_refl) as [_ Rp]. pose proof (obj_at_nth src2segs memc (ch_c C) LAY_Cht _ 4 _ _ Hobjc eq_refl eq_refl) as [_ Rx].
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
assert (HE26 : ew E 26 = Z_to_bv 64 p1) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (HE27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE23 : ew E 23 = Z_to_bv 64 h1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE24 : ew E 24 = Z_to_bv 64 u1) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE10 : ew E 10 = Z_to_bv 64 f1) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok src2segs E (mkSS PC_M5 sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 5136 112 120 [] ] None (mkFacts [(2%nat, mkAF CEIL_MIN (2^63) 4)] [] []))
(mkst regs1 (Z_to_bv 64 PC_M5) memc (seg_rom src2segs))).
{ subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HU2. split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [|constructor]. intros o Ho. apply Hstw. unfold sp, sp0 in *. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16. unfold sp, sp0 in *. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_M5) memc (seg_rom src2segs))) in HJ. clearbody E.
assert (MEMX : forall (memX : word -> option byte),
journal src2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac memX mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs memX a = mbyte src2segs memc a) ->
RINV Lc Ac memX mdc /\ rz_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay memX i ha pnew fimg imgl C /\
slot regs0 memX SL_72 ha /\ rz_struct memX C (ch_p C) (ch_x C) (ht_cnt (ch_H C))).
{ intros memX HJX KX.
assert (KBX : forall b n k, In (b, n) (blocks Lc Ac) -> 0 <= k < n -> mbyte src2segs memX (b + k) = mbyte src2segs memc (b + k)).
{ intros b n k Hb Hk. destruct (heap_blocks src2_msyms MR LAWS Lc Ac memc mdc b n k HHc Hb Hk) as (_ & H1 & H2 & _). apply KX; unfold sp, sp0 in *; lia. }
split. { apply (RINV_MEM Lc Ac memc memX mdc HINV HJX). intros a Ha Hna. apply KX; unfold sp, sp0 in *; lia. }
split. { apply (RZ_MEM_KEPT Lc Ac memc memX mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| | exact (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM)].
- intros a Ha Hs _ Hn2. apply KX; [lia | exact Hn2].
- intros b n k Hb Hk. apply (KBX b n k); [| exact Hk]. apply INB. apply in_app_iff. left. apply (keepb_sub r g bef beffmt s N img fmt rest). exact Hb. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KX; unfold sp, sp0 in *; lia. }
apply (rz_struct_kept r g bef beffmt s N img fmt rest memc memX pnew fimg C); [exact RZS|]. intros b n k Hb Hk. apply (KBX b n k); [| exact Hk]. apply INB. apply in_app_iff. left. exact Hb. }
assert (ARRF : forall ss ms', st_ok src2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_FAIL ->
journal src2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms') a = mbyte src2segs memc a) ->
slot regs0 (ms_mem ms') SL_112 f1 ->
(p1 = 0 \/ x1 = 0 \/ h1 = 0 \/ u1 = 0 \/ f1 = 0) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 9; 20; 8; 21; 22; 24; 23; 27; 26; 18]%bv = true ->
SR src2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hrv Hpc HJ' KX S112 Hz0 QK.
pose proof (regs_kept_of_st_ok src2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
destruct (MEMX (ms_mem ms') HJ' KX) as (HINV' & RZM' & S72' & RZS').
rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc. apply (KFAIL (ms_regs ms') Lc Ac (ms_mem ms') mdc p1 x1 h1 u1 f1). unfold at_FAIL.
split; [exact HINV'|]. split; [exact HRZF|].
split. { unfold rz_regs, rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G22. }
split. { unfold chk_regs.
rewrite (GK 24%bv ltac:(cbv; auto 20)), (GK 23%bv ltac:(cbv; auto 20)), (GK 27%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 18%bv ltac:(cbv; auto 20)).
repeat (split; [assumption|]). exact G18. }
split; [exact Hz0|]. split; [exact RZM'|]. split; [exact S72'|]. split; [exact S112|]. split; [exact RZS' | exact RZB]. }
assert (ARRC : forall ss ms', st_ok src2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_C0 ->
journal src2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms') a = mbyte src2segs memc a) ->
slot regs0 (ms_mem ms') SL_112 f1 ->
p1 <> 0 -> x1 <> 0 -> h1 <> 0 -> u1 <> 0 -> f1 <> 0 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 9; 20; 8; 21; 22; 24; 23; 27; 26; 18]%bv = true ->
SR src2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hrv Hpc HJ' KX S112 N1 N2 N3 N4 N5 QK.
pose proof (regs_kept_of_st_ok src2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
destruct (MEMX (ms_mem ms') HJ' KX) as (HINV' & RZM' & S72' & RZS').
rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc. apply (KC0 (ms_regs ms') Lc Ac (ms_mem ms') mdc p1 x1 h1 u1 f1). unfold at_C0.
split; [exact HINV'|]. split; [exact HRZF|].
split. { unfold rz_regs, rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)), (GK 22%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G22. }
split. { unfold chk_regs.
rewrite (GK 24%bv ltac:(cbv; auto 20)), (GK 23%bv ltac:(cbv; auto 20)), (GK 27%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 18%bv ltac:(cbv; auto 20)).
repeat (split; [assumption|]). exact G18. }
split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|].
split; [exact RZM'|]. split; [exact S72'|]. split; [exact S112|]. split; [exact RZS'|].
unfold rz_blocks. eapply Permutation_trans; [exact RZB|]. unfold rbk, optb.
destruct (Z.eqb_spec p1 0); [lia|]. destruct (Z.eqb_spec x1 0); [lia|]. destruct (Z.eqb_spec h1 0); [lia|]. destruct (Z.eqb_spec u1 0); [lia|]. destruct (Z.eqb_spec f1 0); [lia|].
cbn [app]. apply Permutation_refl. }
Ltac s112 HS HU2 HE10 Rf1 :=
unfold slot, SL_112; lazymatch type of HS with st_ok _ ?E0 _ _ =>
apply (st_chunk_word_g src2segs E0 _ _ 0%nat _ 2%nat 112 (SOff 10 0) _ _ HS eq_refl eq_refl ltac:(cbn [r_chunks]; cbv [In]; auto 20) HU2);
[cbn [sv_denot]; rewrite Z.add_0_r, HE10, Z_to_bv_bv_unsigned; reflexivity | exact Rf1] end.
Ltac wrw HU2 := eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold sp, sp0 in *; lia | apply wr_ok_nil].
jrun LAWS src2tbl_ok HS HJ. { wrw HU2. }
cbn [ms_mem mkst] in HF.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF; [reflexivity | rewrite HU2; lia]. }
jbranch src2tbl HS.
{ rewrite branch_eq_U, (U_atom E 26 p1 HE26), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
jrun_to LAWS src2tbl_ok HS HJ PC_FAIL. { wrw HU2. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms0) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF0; [exact (K0 a Ha Hna) | rewrite HU2; lia]. }
apply (ARRF _ _ HS eq_refl eq_refl HJ K1); [s112 HS HU2 HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 26 p1 HE26), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
jrun LAWS src2tbl_ok HS HJ. { wrw HU2. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms0) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF0; [exact (K0 a Ha Hna) | rewrite HU2; lia]. }
jbranch src2tbl HS.
{ rewrite branch_eq_U, (U_atom E 27 x1 HE27), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
jrun_to LAWS src2tbl_ok HS HJ PC_FAIL. { wrw HU2. }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms1) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF1; [exact (K1 a Ha Hna) | rewrite HU2; lia]. }
apply (ARRF _ _ HS eq_refl eq_refl HJ K2); [s112 HS HU2 HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 27 x1 HE27), U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
jrun LAWS src2tbl_ok HS HJ. { wrw HU2. }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms1) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF1; [exact (K1 a Ha Hna) | rewrite HU2; lia]. }
jbranch src2tbl HS.
{ rewrite branch_eq_U, (U_atom E 23 h1 HE23), U_lit in Hc1 by lia. apply Z.eqb_eq in Hc1.
jrun_to LAWS src2tbl_ok HS HJ PC_FAIL. { wrw HU2. }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms2) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF2; [exact (K2 a Ha Hna) | rewrite HU2; lia]. }
apply (ARRF _ _ HS eq_refl eq_refl HJ K3); [s112 HS HU2 HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 23 h1 HE23), U_lit in Hc1 by lia. apply Z.eqb_neq in Hc1.
jrun LAWS src2tbl_ok HS HJ. { wrw HU2. }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms2) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF2; [exact (K2 a Ha Hna) | rewrite HU2; lia]. }
jbranch src2tbl HS.
{ rewrite branch_eq_U, (U_atom E 24 u1 HE24), U_lit in Hc2 by lia. apply Z.eqb_eq in Hc2.
jrun_to LAWS src2tbl_ok HS HJ PC_FAIL. { wrw HU2. }
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms3) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF3; [exact (K3 a Ha Hna) | rewrite HU2; lia]. }
apply (ARRF _ _ HS eq_refl eq_refl HJ K4); [s112 HS HU2 HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 24 u1 HE24), U_lit in Hc2 by lia. apply Z.eqb_neq in Hc2.
jrun LAWS src2tbl_ok HS HJ. { wrw HU2. }
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms3) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF3; [exact (K3 a Ha Hna) | rewrite HU2; lia]. }
jbranch src2tbl HS.
{ rewrite branch_eq_U, (U_atom E 10 f1 HE10), U_lit in Hc3 by lia. apply Z.eqb_eq in Hc3.
jrun_to LAWS src2tbl_ok HS HJ PC_FAIL. { wrw HU2. }
assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms4) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF4; [exact (K4 a Ha Hna) | rewrite HU2; lia]. }
apply (ARRF _ _ HS eq_refl eq_refl HJ K5); [s112 HS HU2 HE10 Rf1 | lia | vm_compute; reflexivity]. }
rewrite branch_eq_U, (U_atom E 10 f1 HE10), U_lit in Hc3 by lia. apply Z.eqb_neq in Hc3.
jrun_to LAWS src2tbl_ok HS HJ PC_C0. { wrw HU2. }
assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + 112 <= a < SP + 120) -> mbyte src2segs (ms_mem ms4) a = mbyte src2segs memc a).
{ intros a Ha Hna. mb_frame_g HF4; [exact (K4 a Ha Hna) | rewrite HU2; lia]. }
apply (ARRC _ _ HS eq_refl eq_refl HJ K5); [s112 HS HU2 HE10 Rf1 | exact Hc | exact Hc0 | exact Hc1 | exact Hc2 | exact Hc3 | vm_compute; reflexivity].
Qed.
End S6.
End d.
End c.
