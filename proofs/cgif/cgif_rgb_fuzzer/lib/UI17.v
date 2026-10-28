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
UI1e UI39 UI1i UI20 UI59 UI56 YI0x UI57
UI1h UI1g UI16 UI19.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition AF_E2 : Z := Eval vm_compute in (ubs2_A_cgif_addframe + 0x438).
Definition AF_E3 : Z := Eval vm_compute in (ubs2_A_cgif_addframe + 0x490).
Definition E3_regions (z4 : bool) : list YQ0b.region :=
[ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ;
YQ0b.mkRegion (Some 8%nat) 88 92 88 92 [] ;
af_Rcf ] ++
(if z4 then [] else [ YQ0b.mkRegion (Some 18%nat) 33 34 33 34 [] ]).
Definition ss_E3 (z4 : bool) : sstate :=
mkSS AF_E3 (if z4 then sr_set sr_atoms 19%bv (SLit 0) else sr_atoms)
(E3_regions z4)
None (mkFacts (af_facts ++ (if z4 then [] else [(19%nat, mkAF 1 (2^64 - 1) 0); (10%nat, mkAF 4096 (2^64 - 1) 0)])) [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma af_E3 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z))
(i : nat) (fn : frame_st) (cfp lpal img fattr fgen delay nlp tidx t4 : Z),
let sp0 := spZ regs0 in
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
nth_error (cg_frames s) i = Some (Some fn) ->
obj_at ubs2segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
(forall a, g <= a < g + CGIF_SIZE -> inFP FP a) ->
(forall blc k, In (fr_ptr fn, FRAME_SIZE) blc -> 0 <= k < FRAME_SIZE -> wr_byte ADDFRAME_STK sp0 FP (blocks L A) blc (fr_ptr fn + k)) ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 18 = Z_to_bv 64 (fr_ptr fn) -> getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 ->
getr regs1 10 = Z_to_bv 64 (g + 8 * Z.of_nat i) ->
af_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_E3) memc (seg_rom ubs2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP i fn cfp lpal img fattr fgen delay nlp tidx t4 sp0
HJ Hid Hra0 Hal16 Hat Hwf Hgeom Hifn Hcf Hcf8 Hcflo Hcfhi HFPg HWfn HB HSV G2 G8 G9 G18 G19 Rt4 G10 HUT.
pose proof Hwf as (Hlen & _).
assert (Hih3 : (i < 3)%nat) by (rewrite <- Hlen; apply (proj1 (nth_error_Some _ _)); rewrite Hifn; discriminate).
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hfin : In (Some fn) (cg_frames s)) by (eapply nth_error_In; exact Hifn).
destruct (af_cgif_geom API Lc Ac memc mdc g s N (CB ++ rest) HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom fn Hfin) as (Hf0 & Hf1 & Hfg).
pose proof (af_raw_frame_sep API Lc Ac memc mdc g s N (CB ++ rest) fn HH0 HB Hfin) as Hfr_raw.
destruct (af_frame_geom API Lc Ac memc mdc g s N (CB ++ rest) fn HH0 HB Hfin) as (Hfblk & _ & _).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf.
pose proof (Rcf 6%nat tidx eq_refl) as Rtidx. cbn [nth snd LAY_FrameConfig Z.of_N] in Rtidx.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HKr regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j r, _ -> _ -> ew E n = _) as HKr.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HC.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr fn) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
assert (HR1 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 8%nat) 88 92 88 92 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HR2.
assert (HR3 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 18%nat) 33 34 33 34 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_ptr fn) FRAME_SIZE o HH0 Hfblk ltac:(lia))). }
assert (HRS : forall z4, Forall (region_ok ubs2segs E memc) (E3_regions z4)).
{ intros [|]; unfold E3_regions; cbn [app]; repeat (constructor; [assumption|]); constructor. }
assert (HPD : forall z4, pairwise_disjoint E (E3_regions z4)).
{ intros [|]; unfold E3_regions, af_Rcf; cbn [app pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite ?HU2, ?HU8, ?HU9, ?HU18; repeat split; lia. }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HWR : forall z4 blc, In (g, CGIF_SIZE) blc -> In (fr_ptr fn, FRAME_SIZE) blc ->
wr_ok E (E3_regions z4) ADDFRAME_STK sp0 FP (blocks L A) blc).
{ intros z4 blc Hg' Hf'. unfold E3_regions. cbn [app].
apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_block with (m := CGIF_SIZE);
[ reflexivity | exact HU8 | exact Hg' | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply HFPg; lia | ].
apply wr_ok_cons_ro; [cbn; lia|].
destruct z4; [apply wr_ok_nil|].
eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | exact HU18 | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (fr_ptr fn + (a - fr_ptr fn)) by lia. apply HWfn; [exact Hf' | lia]. }
destruct (Z.eq_dec t4 0) as [Ht4|Ht4].
-
assert (HS : st_ok ubs2segs E (ss_E3 true) (mkst regs1 (Z_to_bv 64 AF_E3) memc (seg_rom ubs2segs))).
{ unfold ss_E3. subst E. apply entry_st_ok_gen; [| vm_compute; reflexivity | exact (HRS true) | exact (HPD true) | rewrite app_nil_r; exact HFA].
apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; rewrite G19, Ht4; reflexivity]. }
clear HRS HPD HFA HR0 HR1 HR2 HR3.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_E3) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ AF_RET. { wr_norm. apply (HWR true); [exact Hgin | exact Hfblk]. }
cbn [ms_mem mkst] in HF.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (af_ret API IMG L A mem md regs0 rg Lc Ac mm mdc g N s0 (set_cur s 0) CB rest FP) end;
[ exact HJ | exact Hid | exact Hra0 | exact Hal16 | | apply set_cur_wf; exact Hwf | exact Hgeom | rewrite set_cur_blocks; exact HB | | | ].
+ apply (cgif_at_set_cur memc _ g s 0 Hat).
* intros k Hk Hnk. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
* intros k Hk. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
* intros f k Hin Hk. destruct (Hfgeom f Hin) as (F0 & F1 & F2).
destruct (In_nth_error _ _ Hin) as [j Hj].
destruct (Nat.eq_dec j i) as [->|Hne].
{ rewrite Hifn in Hj. injection Hj as ->. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity. }
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) i j fn f HH0 HB Hifn Hj ltac:(lia)) as Hsep.
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
* rewrite <- HU8. lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (proj1 (st_field ubs2segs E _ _ 1%nat _ 8%nat _ 88 4%N (SLit 0) 0 HS eq_refl eq_refl ltac:(cbv; auto 10) eq_refl eq_refl ltac:(cbn; lia) ltac:(cbn; lia))) end.
* lia.
+ apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ split; [|split; [|split; [|split; [|split; [|split]]]]].
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
-
assert (HS : st_ok ubs2segs E (ss_E3 false) (mkst regs1 (Z_to_bv 64 AF_E3) memc (seg_rom ubs2segs))).
{ assert (HF23 : atoms_ok E [(19%nat, mkAF 1 (2^64 - 1) 0); (10%nat, mkAF 4096 (2^64 - 1) 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE 19%nat 19%bv eq_refl), G19, unsigned_lit_small by lia.
rewrite (HE 10%nat 10%bv eq_refl), G10, unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
unfold ss_E3. subst E. apply entry_st_ok; [vm_compute; reflexivity | exact (HRS false) | exact (HPD false) |].
cbn [app]. apply atoms_ok_app; [exact HFA | exact HF23]. }
clear HRS HPD HFA HR0 HR1 HR2 HR3.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_E3) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ AF_RET. { wr_norm. apply (HWR false); [exact Hgin | exact Hfblk]. }
cbn [ms_mem mkst] in HF.
set (fn' := set_fr_tidx fn tidx).
assert (Hnew : obj_at ubs2segs (ms_mem ms) (fr_ptr fn') LAY_Frame (frame_vals fn')).
{ subst fn'. cbn [fr_ptr set_fr_tidx].
eapply (obj_at_upd ubs2segs memc (ms_mem ms) (fr_ptr fn) LAY_Frame FRAME_SIZE (frame_vals fn) _ [8%nat] [(33, 34)] (Hfrs fn Hfin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros k Hk Hw. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; cbn in Hw; first [lia | destruct (Z.leb_spec 33 k); destruct (Z.ltb_spec k 34); cbn in Hw; try discriminate; lia]). reflexivity.
- intros j f v' [<-|[]] Hf Hv'. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-.
rewrite <- HU18. eapply (st_field ubs2segs E _ _ 3%nat _ 18%nat _ 33 1%N _ tidx HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
rewrite denot_lit_U. f_equal. rewrite U_zext. ew_havocA. rewrite (U_atom _ 50 tidx (HC 50%nat 6%nat tidx eq_refl eq_refl)) by lia.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; left; reflexivity] |]). reflexivity. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (af_ret API IMG L A mem md regs0 rg Lc Ac mm mdc g N s0 (set_cur (upd_frame s i fn') 0) CB rest FP) end;
[ exact HJ | exact Hid | exact Hra0 | exact Hal16 |
| apply set_cur_wf; apply (cgif_wf_upd_frame s N i fn fn' Hwf Hifn); pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hfwf); apply (frame_wf_fields (cg_attr s) fn fn' (Hfwf fn Hfin)); reflexivity
| exact Hgeom | rewrite set_cur_blocks, (cgif_blocks_upd_frame g s N i fn fn' Hifn eq_refl); exact HB | | | ].
+ split; [|split].
* rewrite cgif_vals_set_cur_ls, (cgif_vals_upd_frame s i fn fn' Hifn eq_refl).
eapply (obj_at_upd ubs2segs memc (ms_mem ms) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [15%nat] [(88, 92)] Hobj (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
-- intros k Hk Hw. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; cbn in Hw; first [lia | destruct (Z.leb_spec 88 k); destruct (Z.ltb_spec k 92); cbn in Hw; try discriminate; lia]). reflexivity.
-- intros j f v' [<-|[]] Hf Hv'. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-.
rewrite <- HU8. eapply (st_field ubs2segs E _ _ 1%nat _ 8%nat _ 88 4%N (SLit 0) 0 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
-- intros j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; left; reflexivity] |]). reflexivity.
* cbn [set_cur upd_frame set_frames cg_raw].
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
* cbn [set_cur cg_frames]. change (list_set (cg_frames s) i (Some fn')) with (cg_frames (upd_frame s i fn')).
apply (frames_at_upd memc (ms_mem ms) s i (Some fn) fn' Hfrs Hifn Hnew).
intros j x Hj Hne k Hk.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) i j fn x HH0 HB Hifn Hj ltac:(lia)) as Hsep.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
+ apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ split; [|split; [|split; [|split; [|split; [|split]]]]].
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
Qed.
Definition cond_a2 (z2 : bool) : acond := mkAC (if z2 then BC_EQ else BC_NE) (SAlu ALU_AND (SExt false 8 (SOff 46 0)) (SLit 2)) (SLit 0).
Lemma land_low_mod : forall x m k, 0 <= k -> 0 <= m < 2 ^ k -> Z.land (x mod 2 ^ k) m = Z.land x m.
Proof.
intros x m k Hk Hm. rewrite <- (Z.land_ones x k) by lia. rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Definition ss_E2a : sstate :=
mkSS AF_E2 sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rcf ] None (mkFacts af_facts [cond_a2 true] []).
Definition ss_E2b (i : nat) : sstate :=
mkSS AF_E2 (sr_set sr_atoms 20%bv (SLit (Z.of_nat i)))
[ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ;
(if Nat.eqb i 1 then af_Rg_part 0 88 0 0 (Some 0) None None None else af_Rg_part 0 88 0 0 None (Some 0) None None) ;
af_Rcf ;
YQ0b.mkRegion (Some 18%nat) 33 34 33 34 [] ]
None (mkFacts (af_facts ++ [(10%nat, mkAF 4096 (2^64 - 1) 0)]) [cond_a2 false] []).
Definition ss_E2c (i : nat) : sstate :=
mkSS AF_E2 (sr_set sr_atoms 20%bv (SLit (Z.of_nat i)))
[ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ;
af_Rg_part 0 88 0 0 None None None None ;
af_Rcf ;
YQ0b.mkRegion (Some 18%nat) 33 34 33 34 [] ;
af_Rfr_part (50 + i) 68 20 24 20 24 ;
af_Rfr_part (50 + i) 68 32 33 32 33 ]
None (mkFacts (af_facts ++ [((50 + i)%nat, mkAF 4096 (CEIL_MAX - 40) 4); (10%nat, mkAF 4096 (2^64 - 1) 0)]) [cond_a2 false] []).
Lemma af_E2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z))
(i : nat) (fn : frame_st) (op : option frame_st) (cfp lpal img fattr fgen delay nlp tidx t4 : Z),
let sp0 := spZ regs0 in
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
(i = 1%nat \/ i = 2%nat) ->
nth_error (cg_frames s) i = Some (Some fn) -> nth_error (cg_frames s) (i - 1) = Some op ->
obj_at ubs2segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
(forall a, g <= a < g + CGIF_SIZE -> inFP FP a) ->
(forall fp a, op = Some fp -> fr_ptr fp <= a < fr_ptr fp + FRAME_SIZE -> inFP FP a) ->
(forall blc k, In (fr_ptr fn, FRAME_SIZE) blc -> 0 <= k < FRAME_SIZE -> wr_byte ADDFRAME_STK sp0 FP (blocks L A) blc (fr_ptr fn + k)) ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 18 = Z_to_bv 64 (fr_ptr fn) -> getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 ->
getr regs1 20 = Z_to_bv 64 (Z.of_nat i) -> getr regs1 10 = Z_to_bv 64 (g + 8 * Z.of_nat i) ->
af_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_E2) memc (seg_rom ubs2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP i fn op cfp lpal img fattr fgen delay nlp tidx t4 sp0
HJ Hid Hra0 Hal16 Hat Hwf Hgeom Hi Hifn Hiop Hcf Hcf8 Hcflo Hcfhi HFPg HFPp HWfn HB HSV G2 G8 G9 G18 G19 Rt4 G20 G10 HUT.
assert (Hih3 : (i < 3)%nat) by (clear - Hi; lia).
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hfin : In (Some fn) (cg_frames s)) by (eapply nth_error_In; exact Hifn).
destruct (af_cgif_geom API Lc Ac memc mdc g s N (CB ++ rest) HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom fn Hfin) as (Hf0 & Hf1 & Hfg).
pose proof (af_raw_frame_sep API Lc Ac memc mdc g s N (CB ++ rest) fn HH0 HB Hfin) as Hfr_raw.
destruct (af_frame_geom API Lc Ac memc mdc g s N (CB ++ rest) fn HH0 HB Hfin) as (Hfblk & _ & _).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf.
pose proof (Rcf 6%nat tidx eq_refl) as Rtidx. cbn [nth snd LAY_FrameConfig Z.of_N] in Rtidx.
pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. cbn [nth snd LAY_FrameConfig Z.of_N] in Rfattr.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (more := match op with Some fp => frame_vals fp | None => [] end).
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s more).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HKr regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j r, _ -> _ -> ew E n = _) as HKr.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (af_HM regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr fn) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HR2.
assert (HR3 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 18%nat) 33 34 33 34 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_ptr fn) FRAME_SIZE o HH0 Hfblk ltac:(lia))). }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HF10 : atoms_ok E [(10%nat, mkAF 4096 (2^64 - 1) 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE 10%nat 10%bv eq_refl), G10, unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
assert (CONT : forall ss ms' (s2 : cgif_st) (fn2 : frame_st),
st_ok ubs2segs E ss ms' -> ss_pc ss = AF_E3 -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 10%bv = SOff 10 0 -> sr_get (ss_regs ss) 18%bv = SOff 18 0 ->
sr_get (ss_regs ss) 19%bv = SOff 19 0 -> sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
cgif_at (ms_mem ms') g s2 -> cgif_wf s2 N -> same_geom s2 s0 ->
nth_error (cg_frames s2) i = Some (Some fn2) -> fr_ptr fn2 = fr_ptr fn ->
cgif_blocks g s2 N = cgif_blocks g s N ->
obj_at ubs2segs (ms_mem ms') cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
af_saved_ok (ms_mem ms') sp0 regs0 ->
SR ubs2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 CB rest FP L A mem md)).
{ intros ss ms' s2 fn2 HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q10 Q18 Q19 Q23 Q24 Q25 Q26 Q27 HJ' Hat' Hwf' Hgeom' Hifn' Hptr Hblk Hcf' HSV'.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs2segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_E3 L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s2 CB rest FP i fn2 cfp lpal img fattr fgen delay nlp tidx t4);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Hat' | exact Hwf' | exact Hgeom' | exact Hifn' | exact Hcf' | exact Hcf8 | exact Hcflo | exact Hcfhi
| exact HFPg | rewrite Hptr; exact HWfn | rewrite Hblk; exact HB | exact HSV'
| apply (RG _ _ _ Q2); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| apply (RG _ _ _ Q9); rewrite (HE 9%nat 9%bv eq_refl); exact G9
| apply (RG _ _ _ Q18); rewrite (HE 18%nat 18%bv eq_refl), Hptr; exact G18
| apply (RG _ _ _ Q19); rewrite (HE 19%nat 19%bv eq_refl); exact G19
| exact Rt4
| apply (RG _ _ _ Q10); rewrite (HE 10%nat 10%bv eq_refl); exact G10
| split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24); rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25); rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ] ]. }
destruct (Z.eq_dec (Z.land fattr 2) 0) as [Hz2|Hz2].
-
assert (HCT : conds_ok E [cond_a2 true]).
{ cbn [conds_ok]. split; [|exact I].
unfold acond_ok, cond_a2. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U_and_lit, U_lit by lia.
rewrite U_zext, (U_atom _ 46 fattr (HC 46%nat 2%nat fattr eq_refl eq_refl)) by lia.
change (Z.of_N 8) with 8. rewrite land_low_mod by lia. rewrite Hz2. reflexivity. }
assert (HPDa : pairwise_disjoint E (ss_mem ss_E2a)).
{ cbn [ss_mem ss_E2a]. unfold af_Rcf. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite ?HU2, ?HU9. repeat split; lia. }
assert (HS : st_ok ubs2segs E ss_E2a (mkst regs1 (Z_to_bv 64 AF_E2) memc (seg_rom ubs2segs))).
{ unfold ss_E2a. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR2 | constructor]]
| exact HPDa |].
split; [exact HFA|]. split; [exact HCT | exact I]. }
clear HR0 HR2 HR3 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_E2) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ AF_E3. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmem : forall a, mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
apply (CONT _ _ s fn HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ); try assumption; try reflexivity.
+ split; [|split].
* eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply Hmem].
* eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply Hmem].
* intros f Hf. eapply obj_at_transport_range; [exact (Hfrs f Hf) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply Hmem].
+ eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply Hmem].
+ apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply Hmem].
-
assert (HCF : conds_ok E [cond_a2 false]).
{ cbn [conds_ok]. split; [|exact I].
unfold acond_ok, cond_a2. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, U_and_lit, U_lit by lia.
rewrite U_zext, (U_atom _ 46 fattr (HC 46%nat 2%nat fattr eq_refl eq_refl)) by lia.
change (Z.of_N 8) with 8. rewrite land_low_mod by lia. destruct (Z.eqb_spec (Z.land fattr 2) 0); [lia | reflexivity]. }
assert (HWR18 : forall blc, In (fr_ptr fn, FRAME_SIZE) blc -> forall a, fr_ptr fn + 33 <= a < fr_ptr fn + 34 -> wr_byte ADDFRAME_STK sp0 FP (blocks L A) blc a).
{ intros blc Hb a Ha. replace a with (fr_ptr fn + (a - fr_ptr fn)) by lia. apply HWfn; [exact Hb | lia]. }
destruct op as [fp|].
+
assert (Hfpin : In (Some fp) (cg_frames s)) by (eapply nth_error_In; exact Hiop).
destruct (Hfgeom fp Hfpin) as (Hp0 & Hp1 & Hpg).
destruct (af_frame_geom API Lc Ac memc mdc g s N (CB ++ rest) fp HH0 HB Hfpin) as (Hpblk & _ & _).
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) i (i - 1) fn fp HH0 HB Hifn Hiop ltac:(lia)) as Hnp.
pose proof (af_raw_frame_sep API Lc Ac memc mdc g s N (CB ++ rest) fp HH0 HB Hfpin) as Hpr_raw.
pose proof (obj_at_range _ _ _ _ _ (Hfrs fp Hfpin)) as Rfp.
assert (HUp : bv_unsigned (ew E (50 + i)) = fr_ptr fp).
{ rewrite (HX (50 + i)%nat (i - 1)%nat (fr_ptr fp) ltac:(lia)); [apply unsigned_lit_small; lia|].
destruct Hi as [-> | ->]; cbn; rewrite (nth_error_nth' _ None) in Hiop by (pose proof Hwf as (Hlen & _); rewrite Hlen; lia);
injection Hiop as Hn; rewrite Hn; reflexivity. }
assert (HR1 : region_ok ubs2segs E memc (af_Rg_part 0 88 0 0 None None None None)).
{ apply (af_Rg_part_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc g); try exact I; [exact HU8 | lia | lia | exact Hobj | lia | lia | intros k Hk; lia]. }
assert (HR4 : forall lo hi, 0 <= lo -> hi <= 40 -> region_ok ubs2segs E memc (af_Rfr_part (50 + i) 68 lo hi lo hi)).
{ intros lo hi Hlo Hhi. eapply (af_Rfr_part_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc (50 + i) (fr_ptr fp) fp 68);
[exact HUp | reflexivity | lia | lia | exact (Hfrs fp Hfpin) | lia | intros j v Hj; subst more; rewrite Nat.sub_diag; exact Hj | exact Hlo | exact Hhi |].
intros k Hk. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_ptr fp) FRAME_SIZE k HH0 Hpblk ltac:(lia))). }
assert (HPD : pairwise_disjoint E (ss_mem (ss_E2c i))).
{ cbn [ss_mem ss_E2c]. unfold af_Rg_part, af_Rcf, af_Rfr_part. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite ?HU2, ?HU8, ?HU9, ?HU18, ?HUp. repeat split; lia. }
assert (HFA2 : atoms_ok E (af_facts ++ [((50 + i)%nat, mkAF 4096 (CEIL_MAX - 40) 4); (10%nat, mkAF 4096 (2^64 - 1) 0)])).
{ apply atoms_ok_app; [exact HFA|].
apply (atoms_ok_app E [((50 + i)%nat, mkAF 4096 (CEIL_MAX - 40) 4)] [(10%nat, mkAF 4096 (2^64 - 1) 0)]); [| exact HF10].
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HUp. change (2 ^ 4) with 16.
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fp) FRAME_SIZE HH0 Hpblk ltac:(lia)) as (_ & _ & Hp16).
repeat split; lia. }
assert (HS : st_ok ubs2segs E (ss_E2c i) (mkst regs1 (Z_to_bv 64 AF_E2) memc (seg_rom ubs2segs))).
{ unfold ss_E2c. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; rewrite G20; destruct Hi as [-> | ->]; reflexivity].
- destruct Hi as [-> | ->]; vm_compute; reflexivity.
- constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor; [exact HR3|].
constructor; [apply HR4; lia|]. constructor; [apply HR4; lia|]. constructor.
- exact HPD.
- split; [exact HFA2 | split; [exact HCF | exact I]]. }
clear HPD HFA2.
clear HR0 HR1 HR2 HR3 HR4 HFA HF10 HCF.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_E2) memc (seg_rom ubs2segs))) in HJ.
destruct Hi as [-> | ->]; cbn [Nat.add] in HUp.
* jrun_to LAWS ubs2tbl_ok HS HJ AF_E3.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; apply HWR18; exact Hfblk |].
eapply wr_ok_cons_block with (m := FRAME_SIZE); [ reflexivity | exact HUp | exact Hpblk | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply (HFPp fp); [reflexivity | lia] | ].
eapply wr_ok_cons_block with (m := FRAME_SIZE); [ reflexivity | exact HUp | exact Hpblk | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply (HFPp fp); [reflexivity | lia] | ].
apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> (a < fr_ptr fn + 33 \/ fr_ptr fn + 34 <= a) ->
(a < fr_ptr fp + 20 \/ fr_ptr fp + 24 <= a) -> (a < fr_ptr fp + 32 \/ fr_ptr fp + 33 <= a) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha W1 W2 W3. clear - HF Ha W1 W2 W3 HU2 HU8 HU9 HU18 HUp.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18, ?HUp; lia). reflexivity. }
clear HF.
set (fn' := set_fr_tidx fn tidx).
lazymatch type of HS with st_ok _ _ _ ?msf =>
set (gen' := U E (SAlu ALU_AND (SExt false 32 (SOff 71 0)) (SLit (-3))) mod 2 ^ 32) end.
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hnew : obj_at ubs2segs (ms_mem ms) (fr_ptr fn') LAY_Frame (frame_vals fn')).
{ subst fn'. cbn [fr_ptr set_fr_tidx].
eapply (obj_at_upd ubs2segs memc (ms_mem ms) (fr_ptr fn) LAY_Frame FRAME_SIZE (frame_vals fn) _ [8%nat] [(33, 34)] (Hfrs fn Hfin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 _]. apply KEPT; clear - Hk W1 Hnp HFSv Hf0 Hf1 Hac; lia.
- intros j f v' [<-|[]] Hf Hv'. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-.
rewrite <- HU18. eapply (st_field ubs2segs E _ _ 3%nat _ 18%nat _ 33 1%N _ tidx HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
rewrite denot_lit_U. f_equal. rewrite U_zext. ew_havocA. rewrite (U_atom _ 50 tidx (HC 50%nat 6%nat tidx eq_refl eq_refl)) by lia.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; left; reflexivity] |]). reflexivity. }
assert (Hnewp : obj_at ubs2segs (ms_mem ms) (fr_ptr fp') LAY_Frame (frame_vals fp')).
{ subst fp'. cbn [fr_ptr set_fr_gen_disp].
eapply (obj_at_upd ubs2segs memc (ms_mem ms) (fr_ptr fp) LAY_Frame FRAME_SIZE (frame_vals fp) _ [3%nat; 7%nat] [(20, 24); (32, 33)] (Hfrs fp Hfpin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hnp HFSv Hp0 Hp1 Hac; lia.
- intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
+ rewrite <- HUp. eapply (st_field_low ubs2segs E _ _ 4%nat _ 51%nat _ 20 4%N _ _ HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity].
+ rewrite <- HUp. eapply (st_field ubs2segs E _ _ 5%nat _ 51%nat _ 32 1%N (SLit 8) 8 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity. }
apply (CONT _ _ (upd_frame (upd_frame s 1 fn') 0 fp') fn' HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
-- split; [|split].
++ rewrite (cgif_vals_upd_frame _ 0 fp fp') by (first [rewrite nth_error_upd_frame_other by lia; exact Hiop | reflexivity]).
rewrite (cgif_vals_upd_frame s 1 fn fn' Hifn eq_refl).
eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros k Hk. apply KEPT; clear - Hk Hfg Hpg HGSv HFSv Hg0 Hg1 Hac; lia.
++ rewrite !cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hfr_raw Hpr_raw HRSv HFSv Hr0 Hr1 Hac; lia.
++ apply (frames_at_upd2 memc (ms_mem ms) s 1 0 (Some fn) fn' (Some fp) fp' Hfrs Hifn Hiop ltac:(lia) Hnew Hnewp).
intros j x Hj Hj1 Hj2 k Hk.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) 1 j fn x HH0 HB Hifn Hj ltac:(clear - Hj1; lia)) as Hsep1.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) 0 j fp x HH0 HB Hiop Hj ltac:(clear - Hj2; lia)) as Hsep2.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
apply KEPT; clear - Hk Hsep1 Hsep2 X0 X1 HFSv Hac; lia.
-- apply (cgif_wf_upd_frame _ N 0 fp fp'); [apply (cgif_wf_upd_frame s N 1 fn fn' Hwf Hifn) | rewrite nth_error_upd_frame_other by lia; exact Hiop |].
++ pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hfwf). apply (frame_wf_fields (cg_attr s) fn fn' (Hfwf fn Hfin)); reflexivity.
++ rewrite cg_attr_upd_frame. pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hfwf). split; [| right; reflexivity].
cbn [fp' set_fr_gen_disp fr_attr]. exact (proj1 (Hfwf fp Hfpin)).
-- exact Hgeom.
-- rewrite nth_error_upd_frame_other by lia. apply (nth_error_upd_frame_same s 1 (Some fn) fn' Hifn).
-- reflexivity.
-- rewrite (cgif_blocks_upd_frame _ _ N 0 fp fp') by (first [rewrite nth_error_upd_frame_other by lia; exact Hiop | reflexivity]).
apply (cgif_blocks_upd_frame g s N 1 fn fn' Hifn eq_refl).
-- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hf1 Hp1 HASv HFSv Hac; lia.
-- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hf1 Hp1 HASv HFSv Hac; lia.
*
jrun_to LAWS ubs2tbl_ok HS HJ AF_E3.
{ wr_norm. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; apply HWR18; exact Hfblk |].
eapply wr_ok_cons_block with (m := FRAME_SIZE); [ reflexivity | exact HUp | exact Hpblk | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply (HFPp fp); [reflexivity | lia] | ].
eapply wr_ok_cons_block with (m := FRAME_SIZE); [ reflexivity | exact HUp | exact Hpblk | cbn; lia | cbn; lia | cbn [r_wlo r_whi]; intros a Ha; apply (HFPp fp); [reflexivity | lia] | ].
apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> (a < fr_ptr fn + 33 \/ fr_ptr fn + 34 <= a) ->
(a < fr_ptr fp + 20 \/ fr_ptr fp + 24 <= a) -> (a < fr_ptr fp + 32 \/ fr_ptr fp + 33 <= a) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha W1 W2 W3. clear - HF Ha W1 W2 W3 HU2 HU8 HU9 HU18 HUp.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18, ?HUp; lia). reflexivity. }
clear HF.
set (fn' := set_fr_tidx fn tidx).
lazymatch type of HS with st_ok _ _ _ ?msf =>
set (gen' := U E (SAlu ALU_AND (SExt false 32 (SOff 71 0)) (SLit (-3))) mod 2 ^ 32) end.
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hnew : obj_at ubs2segs (ms_mem ms) (fr_ptr fn') LAY_Frame (frame_vals fn')).
{ subst fn'. cbn [fr_ptr set_fr_tidx].
eapply (obj_at_upd ubs2segs memc (ms_mem ms) (fr_ptr fn) LAY_Frame FRAME_SIZE (frame_vals fn) _ [8%nat] [(33, 34)] (Hfrs fn Hfin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 _]. apply KEPT; clear - Hk W1 Hnp HFSv Hf0 Hf1 Hac; lia.
- intros j f v' [<-|[]] Hf Hv'. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-.
rewrite <- HU18. eapply (st_field ubs2segs E _ _ 3%nat _ 18%nat _ 33 1%N _ tidx HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
rewrite denot_lit_U. f_equal. rewrite U_zext. ew_havocA. rewrite (U_atom _ 50 tidx (HC 50%nat 6%nat tidx eq_refl eq_refl)) by lia.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; left; reflexivity] |]). reflexivity. }
assert (Hnewp : obj_at ubs2segs (ms_mem ms) (fr_ptr fp') LAY_Frame (frame_vals fp')).
{ subst fp'. cbn [fr_ptr set_fr_gen_disp].
eapply (obj_at_upd ubs2segs memc (ms_mem ms) (fr_ptr fp) LAY_Frame FRAME_SIZE (frame_vals fp) _ [3%nat; 7%nat] [(20, 24); (32, 33)] (Hfrs fp Hfpin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hnp HFSv Hp0 Hp1 Hac; lia.
- intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
+ rewrite <- HUp. eapply (st_field_low ubs2segs E _ _ 4%nat _ 52%nat _ 20 4%N _ _ HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity].
+ rewrite <- HUp. eapply (st_field ubs2segs E _ _ 5%nat _ 52%nat _ 32 1%N (SLit 8) 8 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity. }
apply (CONT _ _ (upd_frame (upd_frame s 2 fn') 1 fp') fn' HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
-- split; [|split].
++ rewrite (cgif_vals_upd_frame _ 1 fp fp') by (first [rewrite nth_error_upd_frame_other by lia; exact Hiop | reflexivity]).
rewrite (cgif_vals_upd_frame s 2 fn fn' Hifn eq_refl).
eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros k Hk. apply KEPT; clear - Hk Hfg Hpg HGSv HFSv Hg0 Hg1 Hac; lia.
++ rewrite !cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hfr_raw Hpr_raw HRSv HFSv Hr0 Hr1 Hac; lia.
++ apply (frames_at_upd2 memc (ms_mem ms) s 2 1 (Some fn) fn' (Some fp) fp' Hfrs Hifn Hiop ltac:(lia) Hnew Hnewp).
intros j x Hj Hj1 Hj2 k Hk.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) 2 j fn x HH0 HB Hifn Hj ltac:(clear - Hj1; lia)) as Hsep1.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) 1 j fp x HH0 HB Hiop Hj ltac:(clear - Hj2; lia)) as Hsep2.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
apply KEPT; clear - Hk Hsep1 Hsep2 X0 X1 HFSv Hac; lia.
-- apply (cgif_wf_upd_frame _ N 1 fp fp'); [apply (cgif_wf_upd_frame s N 2 fn fn' Hwf Hifn) | rewrite nth_error_upd_frame_other by lia; exact Hiop |].
++ pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hfwf). apply (frame_wf_fields (cg_attr s) fn fn' (Hfwf fn Hfin)); reflexivity.
++ rewrite cg_attr_upd_frame. pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hfwf). split; [| right; reflexivity].
cbn [fp' set_fr_gen_disp fr_attr]. exact (proj1 (Hfwf fp Hfpin)).
-- exact Hgeom.
-- rewrite nth_error_upd_frame_other by lia. apply (nth_error_upd_frame_same s 2 (Some fn) fn' Hifn).
-- reflexivity.
-- rewrite (cgif_blocks_upd_frame _ _ N 1 fp fp') by (first [rewrite nth_error_upd_frame_other by lia; exact Hiop | reflexivity]).
apply (cgif_blocks_upd_frame g s N 2 fn fn' Hifn eq_refl).
-- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hf1 Hp1 HASv HFSv Hac; lia.
-- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hf1 Hp1 HASv HFSv Hac; lia.
+
assert (Hpin : frame_ptr (nth (i - 1) (cg_frames s) None) = 0).
{ rewrite (nth_error_nth' _ None) in Hiop by (pose proof Hwf as (Hlen & _); rewrite Hlen; lia). injection Hiop as Hn. rewrite Hn. reflexivity. }
assert (HR1 : region_ok ubs2segs E memc (if Nat.eqb i 1 then af_Rg_part 0 88 0 0 (Some 0) None None None else af_Rg_part 0 88 0 0 None (Some 0) None None)).
{ destruct Hi as [-> | ->]; cbn [Nat.eqb];
(apply (af_Rg_part_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc g); [exact HU8 | lia | lia | exact Hobj | | | | | lia | lia | intros k Hk; lia]);
first [exact I | symmetry; exact Hpin]. }
assert (HPD : pairwise_disjoint E (ss_mem (ss_E2b i))).
{ cbn [ss_mem ss_E2b]. destruct Hi as [-> | ->]; cbn [Nat.eqb]; unfold af_Rg_part, af_Rcf; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite ?HU2, ?HU8, ?HU9, ?HU18; repeat split; lia. }
assert (HS : st_ok ubs2segs E (ss_E2b i) (mkst regs1 (Z_to_bv 64 AF_E2) memc (seg_rom ubs2segs))).
{ unfold ss_E2b. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; rewrite G20; destruct Hi as [-> | ->]; reflexivity].
- destruct Hi as [-> | ->]; vm_compute; reflexivity.
- constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor; [exact HR3|]. constructor.
- exact HPD.
- split; [apply atoms_ok_app; [exact HFA | exact HF10] | split; [exact HCF | exact I]]. }
clear HPD HR0 HR1 HR2 HR3 HFA HF10 HCF.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_E2) memc (seg_rom ubs2segs))) in HJ.
assert (HWR : forall blc, In (fr_ptr fn, FRAME_SIZE) blc -> forall rg1,
r_whi rg1 <= r_wlo rg1 ->
wr_ok E [YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32); rg1; af_Rcf; YQ0b.mkRegion (Some 18%nat) 33 34 33 34 []] ADDFRAME_STK sp0 FP (blocks L A) blc).
{ intros blc Hb rg1 Hro. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [exact Hro|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; apply HWR18; exact Hb | apply wr_ok_nil]. }
set (fn' := set_fr_tidx fn tidx).
assert (FIN : forall ss ms', st_ok ubs2segs E ss ms' -> ss_pc ss = AF_E3 -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 10%bv = SOff 10 0 -> sr_get (ss_regs ss) 18%bv = SOff 18 0 ->
sr_get (ss_regs ss) 19%bv = SOff 19 0 -> sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
nth_error (ss_mem ss) 3 = Some (YQ0b.mkRegion (Some 18%nat) 33 34 33 34 [mkChunk 33 (CVal 1 (SExt false 8 (SOff 50 0)))]) ->
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> (a < fr_ptr fn + 33 \/ fr_ptr fn + 34 <= a) -> mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
SR ubs2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 CB rest FP L A mem md)).
{ intros ss ms' HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q10 Q18 Q19 Q23 Q24 Q25 Q26 Q27 Hrg3 HJ' KEPT.
assert (Hnew : obj_at ubs2segs (ms_mem ms') (fr_ptr fn') LAY_Frame (frame_vals fn')).
{ subst fn'. cbn [fr_ptr set_fr_tidx].
eapply (obj_at_upd ubs2segs memc (ms_mem ms') (fr_ptr fn) LAY_Frame FRAME_SIZE (frame_vals fn) _ [8%nat] [(33, 34)] (Hfrs fn Hfin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 _]. apply KEPT; clear - Hk W1 HFSv Hf0 Hf1 Hac; lia.
- intros j f v' [<-|[]] Hf Hv'. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-.
rewrite <- HU18. eapply (st_field ubs2segs E _ _ 3%nat _ 18%nat _ 33 1%N _ tidx HS' Hrg3); [reflexivity | left; reflexivity | reflexivity | | cbn; lia | cbn; lia].
rewrite denot_lit_U. f_equal. rewrite U_zext. rewrite (U_atom _ 50 tidx (HC 50%nat 6%nat tidx eq_refl eq_refl)) by lia.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; left; reflexivity] |]). reflexivity. }
apply (CONT _ _ (upd_frame s i fn') fn' HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q10 Q18 Q19 Q23 Q24 Q25 Q26 Q27 HJ').
- split; [|split].
+ rewrite (cgif_vals_upd_frame s i fn fn' Hifn eq_refl).
eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros k Hk. apply KEPT; clear - Hk Hfg HGSv HFSv Hg0 Hg1 Hac; lia.
+ rewrite cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hfr_raw HRSv HFSv Hr0 Hr1 Hac; lia.
+ apply (frames_at_upd memc (ms_mem ms') s i (Some fn) fn' Hfrs Hifn Hnew).
intros j x Hj Hne k Hk.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (CB ++ rest) i j fn x HH0 HB Hifn Hj ltac:(clear - Hne; lia)) as Hsep1.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
apply KEPT; clear - Hk Hsep1 X0 X1 HFSv Hac; lia.
- apply (cgif_wf_upd_frame s N i fn fn' Hwf Hifn).
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hfwf). apply (frame_wf_fields (cg_attr s) fn fn' (Hfwf fn Hfin)); reflexivity.
- exact Hgeom.
- apply (nth_error_upd_frame_same s i (Some fn) fn' Hifn).
- reflexivity.
- apply (cgif_blocks_upd_frame g s N i fn fn' Hifn eq_refl).
- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hf1 HASv HFSv Hac; lia.
- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hf1 HASv HFSv Hac; lia. }
destruct Hi as [-> | ->].
* jrun_to LAWS ubs2tbl_ok HS HJ AF_E3. { wr_norm. apply HWR; [exact Hfblk | cbn; lia]. }
cbn [ms_mem mkst] in HF.
apply (FIN _ _ HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
intros a Ha W1. clear - HF Ha W1 HU2 HU8 HU9 HU18.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
* jrun_to LAWS ubs2tbl_ok HS HJ AF_E3. { wr_norm. apply HWR; [exact Hfblk | cbn; lia]. }
cbn [ms_mem mkst] in HF.
apply (FIN _ _ HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
intros a Ha W1. clear - HF Ha W1 HU2 HU8 HU9 HU18.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
