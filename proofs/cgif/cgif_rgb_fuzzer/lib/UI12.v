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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI39 UI1i UI20 UI59 UI56 YI0x UI57
UI1h UI1g UI16 UI19 UI17 UI18 UI11.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition AF_CF : Z := Eval vm_compute in (ubs2_A_cgif_addframe + 0x2a8).
Definition AF_FREED : Z := Eval vm_compute in (ubs2_A_cgif_addframe + 0x2d0).
Definition ss_CF : sstate :=
mkSS AF_CF sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rg None None None None ] None (mkFacts af_facts [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis FLUSH : flush_spec API.
Lemma af_CF :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(o0 : option frame_st) (f1 f2 : frame_st) (cfp lpal lpa img fattr fgen delay nlp tidx t4 : Z),
let sp0 := spZ regs0 in
let CB := [(img, N)] in
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
cg_frames s = [o0; Some f1; Some f2] ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
obj_at ubs2segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
pal_ok mem sp0 fattr lpal nlp ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 ->
af_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_CF) memc (seg_rom ubs2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP o0 f1 f2 cfp lpal lpa img fattr fgen delay nlp tidx t4 sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom Hfr HnoCT Hcf Hcf8 Hcflo Hcfhi Hlpa HFP HB HSV G2 G8 G9 G23 Rt4 HUT.
pose proof HUT as (G3 & G4 & U23 & U24 & U25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HFLv : FLUSH_STK = 9216) by reflexivity. assert (HFFv : FREEFRAME_STK = 8208) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as (_ & _ & (Hg0 & Hg1 & Hg16)).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (HFPg : forall a, g <= a < g + CGIF_SIZE -> inFP FP a) by (intros a Ha; apply (HFP g CGIF_SIZE a); [left; reflexivity | exact Ha]).
assert (HFPlow : forall a, inFP (blocks_fp (cgif_blocks g s N)) a -> inFP FP a /\ a < alloc_ceiling).
{ intros a Ha. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hab). split; [exact (HFP b n a Hbn Hab)|].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc b n HH0 ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn)) as [_ R1]. lia. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
assert (Ho1 : nth_error (cg_frames s) 1 = Some (Some f1)) by (rewrite Hfr; reflexivity).
assert (Ho2 : nth_error (cg_frames s) 2 = Some (Some f2)) by (rewrite Hfr; reflexivity).
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
pose proof (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc g None None None None HU8 ltac:(lia) ltac:(lia) Hobj I I I I) as HR1.
assert (HPD : pairwise_disjoint E (ss_mem ss_CF)).
{ cbn [ss_mem ss_CF]. unfold af_Rg. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, (HE 9%nat 9%bv eq_refl), G9, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok ubs2segs E ss_CF (mkst regs1 (Z_to_bv 64 AF_CF) memc (seg_rom ubs2segs))).
{ unfold ss_CF. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR0|]. constructor; [exact HR1|]. constructor. }
clear HR0 HR1 HPD HFA.
assert (Hspm : (sp0 - 64) mod 16 = 0) by (replace (sp0 - 64) with (sp0 + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_CF) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_flushFrame. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hm10. jreg HS (11%bv:reg) as Hm11. jreg HS (12%bv:reg) as Hm12.
jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4. jreg HS (1%bv:reg) as Hm1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 64) by (unfold spZ; rewrite Hm2; apply unsigned_lit_small; lia) end.
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2 (r gen' rwcur' : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs2_A_cgif_addframe + 0x2c0)) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 1 gen' rwcur') /\ cgif_wf (flush_upd s 1 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks g s N ++ CB ++ rest) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 64 - FLUSH_STK <= x < sp0 - 64) ->
mbyte ubs2segs mem2 x = mbyte ubs2segs (ms_mem ms) x /\ (writable_at ubs2segs (ms_mem ms) x <-> writable_at ubs2segs mem2 x))).
{ eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FLUSH_STK) (FP1 := blocks_fp (cgif_blocks g s N))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => exists r gen' rwcur' : Z,
st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 1 gen' rwcur') /\ cgif_wf (flush_upd s 1 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks g s N ++ CB ++ rest));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FLUSH_STK; lia | rewrite Hsp; unfold FLUSH_STK; lia | rewrite Hsp; lia | exact Hm4 | exact HFPlow ].
intros HPRE1. eapply SR_mono.
{ eapply (FLUSH Lc Ac _ _ mdc g s N 1%nat f1 (CB ++ rest) HPRE1 Hid); [ | | exact Hwf | left; reflexivity | exact Ho1 | | | exact HB ].
- rewrite Hm10, (HE 8%nat 8%bv eq_refl). exact G8.
- eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K1].
- rewrite Hm11, (HX 52%nat 1%nat _ eq_refl eq_refl), Hfr. reflexivity.
- rewrite Hm12, (HX 51%nat 0%nat _ eq_refl eq_refl). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & gen' & rwcur' & -> & HJc & HP & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
exists r, gen', rwcur'. repeat (split; [assumption|]). exact HB2. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2)).
exists L2, A2, regs2, mem2, md2, r, gen', rwcur'. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
repeat (split; [assumption|]).
pose proof HJc2 as (_ & _ & Hhi2 & _). rewrite Hsp in Hhi2. exact Hhi2. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & gen' & rwcur' & -> & HJ2 & HP2 & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hhi2, HJ2, Hr10, Hat2.
set (s1 := flush_upd s 1 gen' rwcur') in *.
set (f1' := set_fr_gen f1 gen').
assert (Hvals1 : cgif_vals s1 = cgif_vals s) by (subst s1; apply cgif_vals_flush_upd).
assert (Hblk1 : cgif_blocks g s1 N = cgif_blocks g s N) by (subst s1; apply flush_upd_blocks; rewrite Hlen; lia).
assert (Hfr1 : cg_frames s1 = [o0; Some f1'; Some f2]) by (subst s1 f1'; apply frames_flush_upd1; exact Hfr).
assert (Hgeom1 : same_geom s1 s0) by (subst s1; exact Hgeom).
assert (HB2' : Permutation (blocks L2 A2) (cgif_blocks g s1 N ++ CB ++ rest)) by (rewrite Hblk1; exact HB2).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
pose proof Hat2 as (Hobj2 & Hraw2 & Hfrs2). rewrite Hvals1 in Hobj2.
jafter_call_keep HS 68%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor]. eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi2 | lia | lia | unfold FLUSH_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq72. cbn [ms_regs mkst] in Hq72. rewrite Hr10 in Hq72. symmetry in Hq72.
af_add_region HS (af_Rg None None None None).
2:{ apply (af_Rg_okE _ mem2 g s None None None None); try exact I; [ew_havocA; exact HU8 | lia | lia | exact Hobj2 | apply (HX_havoc _ s); [exact HX | lia]]. }
2:{ cbn [ss_mem all_disjoint]. unfold af_Rg, extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_freeFrame. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hf10. rewrite (HX 51%nat 0%nat _ eq_refl eq_refl), Hfr in Hf10. cbn [nth] in Hf10.
jreg HS (2%bv:reg) as Hf2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4. jreg HS (1%bv:reg) as Hf1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp2 : spZ (ms_regs msx) = sp0 - 64) by (unfold spZ; rewrite Hf2; apply unsigned_lit_small; lia) end.
cbn [ms_mem mkst] in HF.
assert (K2 : forall a, mbyte ubs2segs (ms_mem ms0) a = mbyte ubs2segs mem2 a).
{ intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
set (s2 := set_frames s1 [None; Some f1'; Some f2]).
assert (HB2s : Permutation (blocks L2 A2) (match o0 with Some f0 => frame_blocks N f0 | None => [] end ++ cgif_blocks g s2 N ++ CB ++ rest)).
{ subst s2. destruct o0 as [f0|].
- eapply Permutation_trans; [exact HB2'|]. apply (perm_frame0_front g s1 N f0 (Some f1') (Some f2) (CB ++ rest) Hfr1).
- cbn [app]. eapply Permutation_trans; [exact HB2'|]. unfold cgif_blocks. rewrite Hfr1. cbn [cg_raw cg_frames set_frames]. rewrite pal_blocks_set_frames. apply Permutation_refl. }
assert (Hcg2 : forall b n, In (b, n) (cgif_blocks g s2 N ++ CB ++ rest) -> In (b, n) (blocks L2 A2)).
{ intros b n Hbn. apply (Permutation_in _ (Permutation_sym HB2s)). apply in_app_iff. right. exact Hbn. }
assert (Hcgr2 : forall b n, In (b, n) (cgif_blocks g s2 N ++ CB ++ rest) -> 4096 <= b /\ b + n <= alloc_ceiling).
{ intros b n Hbn. exact (blocks_range _ _ LAWS L2 A2 mem2 md2 b n HH2 (Hcg2 b n Hbn)). }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L3 A3 regs3 mem3 md3,
c' = mkCfg (mkst regs3 (Z_to_bv 64 AF_FREED) mem3 (seg_rom ubs2segs)) md3 /\
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md L3 A3 mem3 md3 /\
regs_preserved (ms_regs msx) regs3 /\ st_init_done A3 = true /\
Permutation (blocks L3 A3) (cgif_blocks g s2 N ++ CB ++ rest) /\
(forall b n i, In (b, n) (cgif_blocks g s2 N ++ CB ++ rest) -> 0 <= i < n -> mbyte ubs2segs mem3 (b + i) = mbyte ubs2segs (ms_mem msx) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 64 - FREEFRAME_STK <= x < sp0 - 64) ->
mbyte ubs2segs mem3 x = mbyte ubs2segs (ms_mem msx) x /\ (writable_at ubs2segs (ms_mem msx) x <-> writable_at ubs2segs mem3 x)))
end.
{ destruct o0 as [f0|].
-
assert (Hf0in : In (Some f0) (cg_frames s1)) by (rewrite Hfr1; left; reflexivity).
assert (Hf0in0 : In (Some f0) (cg_frames s)) by (rewrite Hfr; left; reflexivity).
eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := fp_freeFrame (fr_ptr f0) (fr_img f0) N (fr_attr f0) (fr_lpal f0) (3 * fr_nlp f0))
(K := fun L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) => Permutation (blocks L3 A3) (cgif_blocks g s2 N ++ CB ++ rest));
[ exact HS | reflexivity | exact HJ2 | exact Hf1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp2; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp2; unfold FREEFRAME_STK; lia | rewrite Hsp2; lia | exact Hf4 | ].
+ intros HPRE1. eapply SR_mono.
{ eapply (ubs2_freeFrame API IMG _ _ _ _ _ (fr_ptr f0) (frame_vals f0) (fr_img f0) N (fr_attr f0) (fr_lpal f0) (3 * fr_nlp f0) (cgif_blocks g s2 N ++ CB ++ rest) HPRE1);
[ exact Hf10 | | reflexivity | reflexivity | reflexivity | ].
- eapply obj_at_transport_range; [exact (Hfrs2 f0 Hf0in) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply K2].
- eapply Permutation_trans; [exact HB2s|]. unfold frame_blocks, pals_of. cbn [app]. apply Permutation_refl. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJc & HP & HB3).
exists L3, A3, regs3, mem3, md3. split; [rewrite Hf1; reflexivity|]. split; [exact HJc|]. split; [exact HP | exact HB3].
+ intros a Ha. split; [| apply HFPlow; apply inFP_blocks_fp].
all: unfold fp_freeFrame in Ha; apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[first [ apply (HFP (fr_ptr f0) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N f0); [exact Hf0in0 | left; reflexivity] | unfold FRAME_SIZE; lia]
| exists (fr_ptr f0), FRAME_SIZE; split; [apply (frame_blocks_in_cgif g s N f0); [exact Hf0in0 | left; reflexivity] | unfold FRAME_SIZE; lia] ] |];
apply inFP_cons in Ha; destruct Ha as [Ha|Ha];
[first [ apply (HFP (fr_img f0) N a); [apply (frame_blocks_in_cgif g s N f0); [exact Hf0in0 | right; left; reflexivity] | lia]
| exists (fr_img f0), N; split; [apply (frame_blocks_in_cgif g s N f0); [exact Hf0in0 | right; left; reflexivity] | lia] ] |];
(destruct (Z.land (fr_attr f0) 1 =? 0) eqn:Hz; [exfalso; exact (inFP_nil a Ha)|]);
apply inFP_cons in Ha; (destruct Ha as [Ha|Ha]; [|exfalso; exact (inFP_nil a Ha)]);
first [ apply (HFP (fr_lpal f0) (3 * fr_nlp f0) a); [apply (frame_blocks_in_cgif g s N f0); [exact Hf0in0|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia]
| exists (fr_lpal f0), (3 * fr_nlp f0); split; [apply (frame_blocks_in_cgif g s N f0); [exact Hf0in0|]; unfold frame_blocks; rewrite Hz; right; right; left; reflexivity | lia] ]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HB3).
exists L3, A3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
split. { pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
assert (Hg3 : In (g, CGIF_SIZE) (blocks L3 A3)) by (eapply blocks_perm_in; [exact HB3 | left; reflexivity]).
apply blocks_In in Hg3 as (q & _ & Hq). exact (init_done_of_block A3 (q, CGIF_SIZE) (proj1 (proj2 HH3)) Hq). }
split; [exact HB3|].
pose proof HJc3 as (_ & _ & Hhi3 & Hkeep3 & _). rewrite Hsp2 in Hhi3. split; [| exact Hhi3].
intros b n i Hbn Hi.
assert (HsepR : forall x, In x (frame_blocks N f0) -> fst x + snd x <= b \/ b + n <= fst x).
{ intros x Hx. pose proof (heap_sep_app API L2 A2 mem2 md2 (frame_blocks N f0) (cgif_blocks g s2 N ++ CB ++ rest) x (b, n) HH2 HB2s Hx Hbn) as Hs. cbn [fst snd] in Hs. exact Hs. }
apply (Hkeep3 b n i); [exact (Hcg2 b n Hbn) | eapply blocks_perm_in; [exact HB3 |]; destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn] | exact Hi |].
intros Hin. unfold fp_freeFrame in Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(left; reflexivity)); cbn [fst snd] in *; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [pose proof (HsepR _ ltac:(right; left; reflexivity)); cbn [fst snd] in *; lia|].
destruct (Z.land (fr_attr f0) 1 =? 0) eqn:Hz; [exact (inFP_nil _ Hin)|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (inFP_nil _ Hin)].
pose proof (HsepR (fr_lpal f0, 3 * fr_nlp f0) ltac:(unfold frame_blocks; rewrite Hz; right; right; left; reflexivity)). cbn [fst snd] in *. lia.
-
eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FREEFRAME_STK) (FP1 := @nil (Z * Z))
(K := fun L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) => A3 = A2 /\ Permutation (blocks L3 A3) (cgif_blocks g s2 N ++ CB ++ rest));
[ exact HS | reflexivity | exact HJ2 | exact Hf1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp2; exact Hspm | unfold FREEFRAME_STK; lia | rewrite Hsp2; unfold FREEFRAME_STK; lia | rewrite Hsp2; lia | exact Hf4
| intros a Ha; exfalso; exact (inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (ubs2_freeFrame_null API IMG _ _ _ _ _ HPRE1). exact Hf10. }
cbv beta. intros c' (regs3 & mem3 & -> & HJc & HP).
exists L2, A2, regs3, mem3, md2. split; [rewrite Hf1; reflexivity|]. split; [exact HJc|]. split; [exact HP|]. split; [reflexivity|]. cbn [app] in HB2s. exact HB2s. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & -> & HB3).
exists L3, A2, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3|]. split; [exact Hid2|]. split; [exact HB3|].
pose proof HJc3 as (_ & _ & Hhi3 & Hkeep3 & _). rewrite Hsp2 in Hhi3. split; [| exact Hhi3].
intros b n i Hbn Hi. apply (Hkeep3 b n i); [exact (Hcg2 b n Hbn) | eapply blocks_perm_in; [exact HB3 |]; destruct Hbn as [Hbn|Hbn]; [left; symmetry; exact Hbn | right; exact Hbn] | exact Hi | intros Hin; exact (inFP_nil _ Hin)]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hid3 & HB3 & Hkeep3 & Hhi3). clear HJ2.
cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
assert (Hgin3 : In (g, CGIF_SIZE) (blocks L3 A3)) by (eapply blocks_perm_in; [exact HB3 | left; reflexivity]).
jafter_call_keep HS 84%nat regs3 mem3 HP3 [1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor]. eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | unfold FREEFRAME_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ((exists b m, In (b, m) (cgif_blocks g s2 N ++ CB ++ rest) /\ b <= a < b + m) \/ sp0 - 64 <= a) ->
mbyte ubs2segs mem3 a = mbyte ubs2segs mem2 a).
{ intros a Ha Hw. rewrite <- (K2 a). destruct Hw as [(b & m & Hbm & Hab) | Hw].
- replace a with (b + (a - b)) by lia. apply (Hkeep3 b m (a - b) Hbm). lia.
- apply (proj1 (Hhi3 a ltac:(clear - Ha Hw Hceil HASv Hac; lia) ltac:(clear - Hw; lia))). }
assert (Hobj3 : obj_at ubs2segs mem3 g LAY_CGIF (cgif_vals s)).
{ eapply obj_at_transport_range; [exact Hobj2 | exact (proj1 LAY_CGIF_ok) |]. intros k Hk. apply K3; [clear - Hk Hg0 Hg1 HGSv Hac; lia | left; exists g, CGIF_SIZE; split; [left; reflexivity | lia]]. }
af_add_region HS (af_Rg_part 24 96 0 0 None None None None).
2:{ apply (af_Rg_part_okE _ mem3 g s None None None None); try exact I; [ew_havocA; exact HU8 | lia | lia | exact Hobj3 | apply (HX_havoc _ s); [apply (HX_havoc _ s); [exact HX | lia] | lia] | lia | lia | intros k Hk; lia]. }
2:{ cbn [ss_mem all_disjoint]. unfold af_Rg_part, extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
af_add_region HS (af_Rg_part 0 24 0 24 None None None None).
2:{ apply (af_Rg_part_okE _ mem3 g s None None None None); try exact I; [ew_havocA; exact HU8 | lia | lia | exact Hobj3 | apply (HX_havoc _ s); [apply (HX_havoc _ s); [exact HX | lia] | lia] | lia | lia |].
intros k Hk. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem3 md3 g CGIF_SIZE k HH3 Hgin3 ltac:(lia))). }
2:{ cbn [ss_mem all_disjoint]. unfold af_Rg_part, extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
jrun LAWS ubs2tbl_ok HS HJ3.
{ eapply wr_ok_cons_block with (m := CGIF_SIZE); [ reflexivity | ew_havocA; exact HU8 | exact Hgin3 | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | ].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof Hwf2 as (Hlen2 & _ & _ & _ & _ & _ & Hih2 & Hfwf2).
assert (Hf1'in : In (Some f1') (cg_frames s1)) by (rewrite Hfr1; right; left; reflexivity).
assert (Hf2in : In (Some f2) (cg_frames s1)) by (rewrite Hfr1; right; right; left; reflexivity).
assert (Hwf_s2 : cgif_wf s2 N).
{ subst s2. apply cgif_wf_set_frames; [exact Hwf2 | reflexivity | | intros f [Hf|[Hf|[Hf|[]]]]; try discriminate Hf; injection Hf as <-; apply Hfwf2; assumption].
destruct Hih2 as [H1|[H2 _]]; [left; exact H1 | right; split; [exact H2 | discriminate]]. }
assert (Hwf_s3 : cgif_wf (set_frames s1 [Some f1'; Some f2; None]) N).
{ apply cgif_wf_set_frames; [exact Hwf2 | reflexivity | | intros f [Hf|[Hf|[Hf|[]]]]; try discriminate Hf; injection Hf as <-; apply Hfwf2; assumption].
destruct Hih2 as [H1|[H2 _]]; [left; exact H1 | right; split; [exact H2 | discriminate]]. }
assert (Hrin2 : In (cg_raw s, RAW_SIZE) (cgif_blocks g s2 N ++ CB ++ rest)) by (right; left; subst s2 s1; reflexivity).
assert (Hf1blk : In (fr_ptr f1, FRAME_SIZE) (cgif_blocks g s2 N ++ CB ++ rest)).
{ apply in_app_iff. left. apply (frame_blocks_in_cgif g s2 N f1'); [subst s2; right; left; reflexivity | left; reflexivity]. }
assert (Hf2blk : In (fr_ptr f2, FRAME_SIZE) (cgif_blocks g s2 N ++ CB ++ rest)).
{ apply in_app_iff. left. apply (frame_blocks_in_cgif g s2 N f2); [subst s2; right; right; left; reflexivity | left; reflexivity]. }
destruct (af_cgif_geom API L2 A2 mem2 md2 g s1 N _ HH2 HB2') as ((Hr0 & Hr1 & Hrg1) & Hfgeom1 & _).
destruct (Hfgeom1 f1' Hf1'in) as (F10 & F11 & F1g). destruct (Hfgeom1 f2 Hf2in) as (F20 & F21 & F2g). cbn [f1' fr_ptr set_fr_gen] in F10, F11, F1g.
assert (OBJ : forall ssX msX (fr : list (option frame_st)) e0 e1 e2 rg,
st_ok ubs2segs (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) ssX msX ->
nth_error (ss_mem ssX) 0 = Some rg -> r_base rg = Some 8%nat ->
In (mkChunk 0 (CVal 8 e0)) (r_chunks rg) -> In (mkChunk 8 (CVal 8 e1)) (r_chunks rg) -> In (mkChunk 16 (CVal 8 e2)) (r_chunks rg) ->
(forall a, 0 <= a < 2 ^ 64 -> (a < g \/ g + 24 <= a) -> mbyte ubs2segs (ms_mem msX) a = mbyte ubs2segs mem3 a) ->
length fr = 3%nat ->
sv_denot (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) e0 = Z_to_bv 64 (frame_ptr (nth 0 fr None)) ->
sv_denot (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) e1 = Z_to_bv 64 (frame_ptr (nth 1 fr None)) ->
sv_denot (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) e2 = Z_to_bv 64 (frame_ptr (nth 2 fr None)) ->
(forall k, (k < 3)%nat -> 0 <= frame_ptr (nth k fr None) < 2 ^ 64) ->
(forall f, In (Some f) fr -> In (Some f) (cg_frames s2)) ->
cgif_at (ms_mem msX) g (set_frames s1 fr)).
{ intros ssX msX fr e0 e1 e2 rg HSX Hrg Hrb C0 C1 C2 KX Hlfr D0 D1 D2 Rfr Hsub.
assert (HU8X : bv_unsigned (ew (havoc (havoc E 68 (map (getr regs2) CLOB)) 84 (map (getr regs3) CLOB)) 8) = g) by (ew_havocA; exact HU8).
split; [|split].
- rewrite cgif_vals_set_frames, Hvals1.
eapply (obj_at_upd ubs2segs mem3 (ms_mem msX) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [0%nat; 1%nat; 2%nat] [(0, 24)] Hobj3 (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
+ intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 _]. apply KX; clear - Hk W1 Hg0 Hg1 HGSv Hac; lia.
+ intros j f v [<-|[<-|[<-|[]]]] Hf Hv; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-; rewrite <- HU8X.
* eapply (st_field ubs2segs _ _ _ 0%nat _ 8%nat _ 0 8%N e0 _ HSX Hrg Hrb C0); [reflexivity | exact D0 | apply (Rfr 0%nat); lia | cbn; lia].
* eapply (st_field ubs2segs _ _ _ 0%nat _ 8%nat _ 8 8%N e1 _ HSX Hrg Hrb C1); [reflexivity | exact D1 | apply (Rfr 1%nat); lia | cbn; lia].
* eapply (st_field ubs2segs _ _ _ 0%nat _ 8%nat _ 16 8%N e2 _ HSX Hrg Hrb C2); [reflexivity | exact D2 | apply (Rfr 2%nat); lia | cbn; lia].
+ intros j Hj. destruct j as [|[|[|j]]]; [exfalso; apply Hj; cbv; auto | exfalso; apply Hj; cbv; auto | exfalso; apply Hj; cbv; auto |]. reflexivity.
- rewrite raw_vals_set_frames, cg_raw_set_frames.
eapply obj_at_transport_range; [exact Hraw2 | exact (proj1 LAY_Raw_ok) |]. subst s1. cbn [cg_raw flush_upd] in *.
intros k Hk. rewrite (KX (cg_raw s + k)); [| clear - Hk Hr0 Hr1 HRSv Hac; lia | clear - Hk Hrg1 HRSv HGSv; lia].
apply K3; [clear - Hk Hr0 Hr1 HRSv Hac; lia | left; exists (cg_raw s), RAW_SIZE; split; [exact Hrin2 | lia]].
- rewrite cg_frames_set_frames. intros f Hf. pose proof (Hsub f Hf) as Hfs2. subst s2. rewrite cg_frames_set_frames in Hfs2.
destruct Hfs2 as [Hx|[Hx|[Hx|[]]]]; [discriminate Hx | injection Hx as <- | injection Hx as <-].
+ eapply obj_at_transport_range; [exact (Hfrs2 f1' Hf1'in) | exact (proj1 LAY_Frame_ok) |]. cbn [f1' fr_ptr set_fr_gen].
intros k Hk. rewrite (KX (fr_ptr f1 + k)); [| clear - Hk F10 F11 HFSv Hac; lia | clear - Hk F1g HFSv HGSv; lia].
apply K3; [clear - Hk F10 F11 HFSv Hac; lia | left; exists (fr_ptr f1), FRAME_SIZE; split; [exact Hf1blk | lia]].
+ eapply obj_at_transport_range; [exact (Hfrs2 f2 Hf2in) | exact (proj1 LAY_Frame_ok) |].
intros k Hk. rewrite (KX (fr_ptr f2 + k)); [| clear - Hk F20 F21 HFSv Hac; lia | clear - Hk F2g HFSv HGSv; lia].
apply K3; [clear - Hk F20 F21 HFSv Hac; lia | left; exists (fr_ptr f2), FRAME_SIZE; split; [exact Hf2blk | lia]]. }
pose proof (Rg 1%nat _ eq_refl) as R52. pose proof (Rg 2%nat _ eq_refl) as R53. rewrite Hfr in R52, R53. cbn [nth snd LAY_CGIF Z.of_N frame_ptr] in R52, R53.
jbranch ubs2tbl HS; clear Hc.
-
jrun_to LAWS ubs2tbl_ok HS HJ3 AF_RETC.
{ wr_norm. eapply wr_ok_cons_block with (m := CGIF_SIZE); [ reflexivity | ew_havocA; exact HU8 | exact Hgin3 | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | ].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HF0.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> (a < g \/ g + 24 <= a) -> mbyte ubs2segs (ms_mem ms2) a = mbyte ubs2segs mem3 a).
{ intros a Ha W1. clear - HF HF0 Ha W1 HU2 HU8. mb_frame_with HF0 ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8; lia).
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
pose proof (OBJ _ _ [None; Some f1'; Some f2] (SLit 0) (SOff 52 0) (SOff 53 0) _ HS eq_refl eq_refl ltac:(cbv; auto 10) ltac:(cbv; auto 10) ltac:(cbv; auto 10) K4 eq_refl eq_refl) as Hat4.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (af_ret_cur API IMG L A mem md regs0 rg L3 A3 mm md3 g N s0 s2 CB rest FP) end;
[ exact HJ3 | exact Hid3 | exact Hra0 | exact Hal16 | exact HFPg | | exact Hwf_s2 | subst s2; exact Hgeom1 | exact HB3 | | | | ].
+ apply Hat4.
* cbn [nth frame_ptr f1' fr_ptr set_fr_gen sv_denot]. ew_havocA. rewrite Z.add_0_r, (HX 52%nat 1%nat _ eq_refl eq_refl), Hfr, Z_to_bv_bv_unsigned. reflexivity.
* cbn [nth frame_ptr sv_denot]. ew_havocA. rewrite Z.add_0_r, (HX 53%nat 2%nat _ eq_refl eq_refl), Hfr, Z_to_bv_bv_unsigned. reflexivity.
* intros k Hk. destruct k as [|[|[|k]]]; cbn [nth frame_ptr f1' fr_ptr set_fr_gen]; lia.
* intros f Hf. exact Hf.
+ apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. rewrite K4; [| clear - Ha Hceil Hsp063 HASv Hac; lia | clear - Ha Hceil Hg1 HASv HGSv; lia].
rewrite K3; [| clear - Ha Hceil Hsp063 HASv Hac; lia | right; clear - Ha; lia].
rewrite (proj1 (Hhi2 a ltac:(clear - Ha Hceil Hsp063 HASv Hac; lia) ltac:(clear - Ha; lia))). apply K1.
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 2%nat 2%bv eq_refl); exact G2).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8).
+ split; [|split; [|split; [|split; [|split; [|split]]]]].
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact U23).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact U24).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact U25).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
-
jrun_to LAWS ubs2tbl_ok HS HJ3 AF_D.
{ wr_norm. eapply wr_ok_cons_block with (m := CGIF_SIZE); [ reflexivity | ew_havocA; exact HU8 | exact Hgin3 | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | ].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HF0.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> (a < g \/ g + 24 <= a) -> mbyte ubs2segs (ms_mem ms2) a = mbyte ubs2segs mem3 a).
{ intros a Ha W1. clear - HF HF0 Ha W1 HU2 HU8. mb_frame_with HF0 ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8; lia).
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
pose proof (OBJ _ _ [Some f1'; Some f2; None] (SOff 52 0) (SOff 53 0) (SLit 0) _ HS eq_refl eq_refl ltac:(cbv; auto 10) ltac:(cbv; auto 10) ltac:(cbv; auto 10) K4 eq_refl) as Hat4.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (af_D1 API IMG L A mem md regs0 rg L3 A3 mm md3 g N s0 (set_frames s1 [Some f1'; Some f2; None]) rest FP 2%nat (Some f2) cfp lpal lpa img fattr fgen delay nlp tidx t4) end;
[ exact HJ3 | exact Hid3 | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf_s3 | subst s1; exact Hgeom | right; reflexivity | reflexivity | reflexivity
| intros _; discriminate | subst s1; exact HnoCT | | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFPg | | rewrite cgif_blocks_shift; exact HB3 | | | | | | | | ].
+ apply Hat4.
* cbn [nth frame_ptr f1' fr_ptr set_fr_gen sv_denot]. ew_havocA. rewrite Z.add_0_r, (HX 52%nat 1%nat _ eq_refl eq_refl), Hfr, Z_to_bv_bv_unsigned. reflexivity.
* cbn [nth frame_ptr sv_denot]. ew_havocA. rewrite Z.add_0_r, (HX 53%nat 2%nat _ eq_refl eq_refl), Hfr, Z_to_bv_bv_unsigned. reflexivity.
* reflexivity.
* intros k Hk. destruct k as [|[|[|k]]]; cbn [nth frame_ptr f1' fr_ptr set_fr_gen]; lia.
* intros f [Hf|[Hf|[Hf|[]]]]; [| | discriminate Hf]; injection Hf as <-; subst s2; rewrite cg_frames_set_frames; cbv; auto.
+ eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. rewrite K4; [| clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia | clear - Hk Hcflo Hceil Hg1 HASv HGSv Hac; lia].
rewrite K3; [| clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia | right; clear - Hk Hcflo; lia].
rewrite (proj1 (Hhi2 (cfp + k) ltac:(clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia) ltac:(clear - Hk Hcflo; lia))). apply K1.
+ intros f a Hf Ha. rewrite cg_frames_set_frames in Hf. destruct Hf as [Hf|[Hf|[Hf|[]]]]; [injection Hf as <- | injection Hf as <- | discriminate Hf].
* apply (HFP (fr_ptr f1) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N f1); [rewrite Hfr; right; left; reflexivity | left; reflexivity] | exact Ha].
* apply (HFP (fr_ptr f2) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N f2); [rewrite Hfr; right; right; left; reflexivity | left; reflexivity] | exact Ha].
+ apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. rewrite K4; [| clear - Ha Hceil Hsp063 HASv Hac; lia | clear - Ha Hceil Hg1 HASv HGSv; lia].
rewrite K3; [| clear - Ha Hceil Hsp063 HASv Hac; lia | right; clear - Ha; lia].
rewrite (proj1 (Hhi2 a ltac:(clear - Ha Hceil Hsp063 HASv Hac; lia) ltac:(clear - Ha; lia))). apply K1.
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 2%nat 2%bv eq_refl); exact G2).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G23).
+ exact Rt4.
+ reg_nowG HS ltac:(reflexivity).
+ split; [|split; [|split; [|split; [|split; [|split]]]]].
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact U23).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact U24).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact U25).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Qed.
Definition ss_C (ih : Z) (p0 p1 p2 : option Z) (fs : list (nat * afact)) : sstate :=
mkSS AF_C (sr_set sr_atoms 20%bv (SLit ih))
[ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rg p0 p1 p2 (Some ih) ] None (mkFacts (af_facts ++ fs) [] []).
Lemma af_C :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(cfp lpal lpa img fattr fgen delay nlp tidx t4 : Z),
let sp0 := spZ regs0 in
let CB := [(img, N)] in
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
obj_at ubs2segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
pal_ok mem sp0 fattr lpal nlp ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 -> getr regs1 20 = Z_to_bv 64 (cg_ihead s) ->
af_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_C) memc (seg_rom ubs2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx t4 sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom HnoCT Hcf Hcf8 Hcflo Hcfhi Hlpa HFP HB HSV G2 G8 G9 G23 Rt4 G24 HUT.
pose proof HUT as (G3 & G4 & U23 & U24 & U25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _ & Hih & _).
destruct (frames3 s N Hwf) as (o0 & o1 & o2 & Hfr).
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as (_ & Hfgeom & (Hg0 & Hg1 & Hg16)).
assert (HFPg : forall a, g <= a < g + CGIF_SIZE -> inFP FP a) by (intros a Ha; apply (HFP g CGIF_SIZE a); [left; reflexivity | exact Ha]).
assert (HFPfr : forall f a, In (Some f) (cg_frames s) -> fr_ptr f <= a < fr_ptr f + FRAME_SIZE -> inFP FP a).
{ intros f a Hf Ha. apply (HFP (fr_ptr f) FRAME_SIZE a); [apply (frame_blocks_in_cgif g s N f); [exact Hf | left; reflexivity] | exact Ha]. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
assert (HR1 : forall p0 p1 p2,
pin_ok p0 (frame_ptr o0) -> pin_ok p1 (frame_ptr o1) -> pin_ok p2 (frame_ptr o2) ->
region_ok ubs2segs E memc (af_Rg p0 p1 p2 (Some (cg_ihead s)))).
{ intros p0 p1 p2 P0 P1 P2. apply (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc g); [exact HU8 | lia | lia | exact Hobj | | | | exact eq_refl];
rewrite Hfr; cbn [nth]; assumption. }
assert (HPD : forall p0 p1 p2 fs, pairwise_disjoint E (ss_mem (ss_C (cg_ihead s) p0 p1 p2 fs))).
{ intros p0 p1 p2 fs. cbn [ss_mem ss_C]. unfold af_Rg. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8. clear - Hg1 Hceil HASv HGSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, (HE 9%nat 9%bv eq_refl), G9, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HFF : forall (k : nat) f, nth_error (cg_frames s) k = Some (Some f) -> atoms_ok E [((51 + k)%nat, mkAF 4096 (CEIL_MAX - 40) 4)]).
{ intros k f Hk. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
assert (Hkl : (k < 3)%nat) by (rewrite <- Hlen; apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
rewrite (HX (51 + k)%nat k (fr_ptr f) eq_refl).
2:{ unfold cgif_vals. destruct k as [|[|[|k]]]; try lia; cbn [nth_error]; rewrite (nth_error_nth _ _ _ Hk); reflexivity. }
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hk).
destruct (Hfgeom f Hfin) as (F0 & F1 & _).
pose proof (proj1 (af_frame_geom API Lc Ac memc mdc g s N _ f HH0 HB Hfin)) as Hfb.
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 Hfb ltac:(lia)) as (_ & _ & F16).
rewrite unsigned_lit_small by lia. change (2 ^ 4) with 16. repeat split; lia. }
assert (HRG : regs_ok E (sr_set sr_atoms 20%bv (SLit (cg_ihead s))) regs1).
{ apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; exact G24]. }
assert (MK : forall p0 p1 p2 fs,
pin_ok p0 (frame_ptr o0) -> pin_ok p1 (frame_ptr o1) -> pin_ok p2 (frame_ptr o2) -> atoms_ok E fs ->
st_ok ubs2segs E (ss_C (cg_ihead s) p0 p1 p2 fs) (mkst regs1 (Z_to_bv 64 AF_C) memc (seg_rom ubs2segs))).
{ intros p0 p1 p2 fs P0 P1 P2 Hfs. unfold ss_C. apply entry_st_ok_full; [exact HRG | | | exact (HPD p0 p1 p2 fs) | split; [apply atoms_ok_app; [exact HFA | exact Hfs] | split; exact I]].
- destruct Hih as [H1|[H2 _]]; rewrite ?H1, ?H2; vm_compute; reflexivity.
- constructor; [exact HR0|]. constructor; [exact (HR1 p0 p1 p2 P0 P1 P2)|]. constructor. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_C) memc (seg_rom ubs2segs))) in HJ.
assert (TOD : forall ss ms' (i : nat) op, st_ok ubs2segs E ss ms' -> ss_pc ss = AF_D -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 19%bv = SOff 19 0 ->
sr_get (ss_regs ss) 20%bv = SLit (Z.of_nat i) -> sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 ->
sr_get (ss_regs ss) 25%bv = SOff 25 0 -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
(i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some None -> nth_error (cg_frames s) (i - 1) = Some op -> (i = 2%nat -> op <> None) ->
SR ubs2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 CB rest FP L A mem md)).
{ intros ss ms' i op HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q19 Q20 Q23 Q24 Q25 Q26 Q27 HJ' K Hi Hinone Hiop Hi2.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs2segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_D1 API IMG L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP i op cfp lpal lpa img fattr fgen delay nlp tidx t4);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact Hi | exact Hinone | exact Hiop | exact Hi2 | exact HnoCT
| | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFPg | exact HFPfr | exact HB | | | | | | | | ].
- eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K].
- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K].
- apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K].
- apply (RG _ _ _ Q2). rewrite (HE 2%nat 2%bv eq_refl). exact G2.
- apply (RG _ _ _ Q8). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG _ _ _ Q9). rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG _ _ _ Q19). rewrite (HE 19%nat 19%bv eq_refl). exact G23.
- exact Rt4.
- rewrite (st_ok_reg ubs2segs E ss ms' 20%bv HS'), Q20. reflexivity.
- split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); rewrite (HE 23%nat 23%bv eq_refl); exact U23
| apply (RG _ _ _ Q24); rewrite (HE 24%nat 24%bv eq_refl); exact U24
| apply (RG _ _ _ Q25); rewrite (HE 25%nat 25%bv eq_refl); exact U25
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]. }
assert (TOCF : forall ss ms' f1 f2, st_ok ubs2segs E ss ms' -> ss_pc ss = AF_CF -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 19%bv = SOff 19 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
cg_frames s = [o0; Some f1; Some f2] ->
SR ubs2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 CB rest FP L A mem md)).
{ intros ss ms' f1 f2 HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q19 Q23 Q24 Q25 Q26 Q27 HJ' K Hfr12.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs2segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_CF L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP o0 f1 f2 cfp lpal lpa img fattr fgen delay nlp tidx t4);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact Hfr12 | exact HnoCT
| | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB | | | | | | | ].
- eapply (cgif_at_kept memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K].
- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K].
- apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K].
- apply (RG _ _ _ Q2). rewrite (HE 2%nat 2%bv eq_refl). exact G2.
- apply (RG _ _ _ Q8). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG _ _ _ Q9). rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG _ _ _ Q19). rewrite (HE 19%nat 19%bv eq_refl). exact G23.
- exact Rt4.
- split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); rewrite (HE 23%nat 23%bv eq_refl); exact U23
| apply (RG _ _ _ Q24); rewrite (HE 24%nat 24%bv eq_refl); exact U24
| apply (RG _ _ _ Q25); rewrite (HE 25%nat 25%bv eq_refl); exact U25
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]. }
assert (RO : forall p0 p1 p2 fs, wr_ok E (ss_mem (ss_C (cg_ihead s) p0 p1 p2 fs)) ADDFRAME_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros. cbn [ss_mem ss_C]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (NT : forall k, 0 <= k <= 24 -> branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 8 0) (SLit (-1)))) (sv_denot E (SLit k)) = false).
{ intros k Hk. rewrite YI00.branch_ltu_U, (YI01.U_not E 8 g) by first [rewrite (HE 8%nat 8%bv eq_refl); exact G8 | lia].
rewrite YQ0c.U_SLit. unfold zcanon, M64. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia. }
destruct Hih as [Hih1 | [Hih2 Hn1]].
-
rewrite Hih1 in MK, RO. destruct o1 as [f1|].
+ destruct o2 as [f2|].
*
pose proof (MK None None None _ I I I (atoms_ok_app _ _ _ (HFF 1%nat f1 ltac:(rewrite Hfr; reflexivity)) (HFF 2%nat f2 ltac:(rewrite Hfr; reflexivity)))) as HS.
jrun_to LAWS ubs2tbl_ok HS HJ AF_CF. { apply RO. }
jbranch ubs2tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ AF_CF. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs2tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ AF_CF. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOCF _ _ f1 f2 HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| exact Hfr].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
*
pose proof (MK None None (Some 0) _ I I eq_refl (HFF 1%nat f1 ltac:(rewrite Hfr; reflexivity))) as HS.
jrun_to LAWS ubs2tbl_ok HS HJ AF_D. { apply RO. }
jbranch ubs2tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ AF_D. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs2tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ AF_D. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOD _ _ 2%nat (Some f1) HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| right; reflexivity | rewrite Hfr; reflexivity | rewrite Hfr; reflexivity | intros _; discriminate].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
+
pose proof (MK None (Some 0) None [] I eq_refl I ltac:(exact I)) as HS.
jrun_to LAWS ubs2tbl_ok HS HJ AF_D. { apply RO. }
jbranch ubs2tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ AF_D. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOD _ _ 1%nat o0 HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| left; reflexivity | rewrite Hfr; reflexivity | rewrite Hfr; reflexivity | intros H; discriminate H].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
-
rewrite Hfr in Hn1. cbn [nth] in Hn1. destruct o1 as [f1|]; [| exfalso; apply Hn1; reflexivity].
rewrite Hih2 in MK, RO. destruct o2 as [f2|].
+
pose proof (MK None None None _ I I I (HFF 2%nat f2 ltac:(rewrite Hfr; reflexivity))) as HS.
jrun_to LAWS ubs2tbl_ok HS HJ AF_CF. { apply RO. }
jbranch ubs2tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ AF_CF. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOCF _ _ f1 f2 HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| exact Hfr].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
+
pose proof (MK None None (Some 0) [] I I eq_refl ltac:(exact I)) as HS.
jrun_to LAWS ubs2tbl_ok HS HJ AF_D. { apply RO. }
jbranch ubs2tbl HS; [exfalso; rewrite NT in Hc by lia; discriminate Hc | clear Hc].
jrun_to LAWS ubs2tbl_ok HS HJ AF_D. { wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply (TOD _ _ 2%nat (Some f1) HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); [| right; reflexivity | rewrite Hfr; reflexivity | rewrite Hfr; reflexivity | intros _; discriminate].
intros a. unfold mbyte. repeat match goal with H : frame_of ?E1 ?rs ?m1 ?m2 |- _ => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) H); clear H end. reflexivity.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
