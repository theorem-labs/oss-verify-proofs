(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p UI2i UI2h UI24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2q UI2r UI2g UI2a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0d YI0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition dv_stk0 : list YP09.chunk :=
[ mkChunk 112 (CVal 8 (SOff 35 0)); mkChunk 120 (CVal 8 (SOff 34 0)); mkChunk 56 (CVal 8 (SOff 36 0)); mkChunk 104 (CVal 8 (SOff 27 0));
mkChunk 32 (CVal 8 (SOff 14 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 24 (CVal 8 (SOff 15 0)) ].
Definition dv_stk1 : list YP09.chunk :=
[ mkChunk 112 (CVal 8 (SOff 35 0)); mkChunk 120 (CVal 8 (SOff 34 0)); mkChunk 72 (CVal 8 (SOff 9 0)); mkChunk 80 (CVal 8 (SOff 19 0));
mkChunk 104 (CVal 8 (SOff 27 0)); mkChunk 56 (CVal 8 (SOff 36 0)); mkChunk 32 (CVal 8 (SOff 14 0)); mkChunk 16 (CVal 8 (SOff 37 0));
mkChunk 24 (CVal 8 (SOff 15 0)) ].
Definition ss_diff : sstate :=
mkSS FL_DIFF sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 272 72 88 dv_stk0 ;
YP09.mkRegion (Some 18%nat) 16 20 16 16 [mkChunk 16 (CVal 4 (SOff 32 0))] ;
YP09.mkRegion (Some 34%nat) 8 16 8 8 [mkChunk 8 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (18%nat, mkAF 4096 CEIL_MAX 3); (34%nat, mkAF 4096 CEIL_MAX 3); (32%nat, mkAF 0 (2^32 - 1) 0) ] [] []).
Lemma lor_lt_64_d : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= Z.lor x y < 2 ^ 64.
Proof using.
intros x y Hx Hy. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor x y) 0) as [-> | Hnz]; [lia|].
assert (Hpos : 0 < Z.lor x y) by (pose proof (proj2 (Z.lor_nonneg x y) ltac:(lia)); lia).
apply (proj2 (Z.log2_lt_pow2 (Z.lor x y) 64 Hpos)).
rewrite Z.log2_lor by lia.
assert (Z.log2 x < 64). { destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
assert (Z.log2 y < 64). { destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
lia.
Qed.
Lemma U_or_d : forall E a b, U E (SAlu ALU_OR a b) = Z.lor (U E a) (U E b).
Proof using. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. apply lor_lt_64_d; apply U_range. Qed.
Lemma U_zext32_shifts_mod_d : forall E a, U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = U E a mod 2 ^ 32.
Proof using.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (Z.land (zcanon 32) 63) with 32. pose proof (U_range E a) as [R0 R1].
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon at 2. unfold M64.
replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) at 1 by reflexivity.
rewrite Z.mul_mod_distr_r by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
Lemma lor_land4_zero : forall b c u, 0 <= b -> 0 <= c -> 0 <= u <= 1 ->
(Z.lor (Z.land (Z.lor b c) 4) u = 0 <-> Z.land b 4 = 0 /\ Z.land c 4 = 0 /\ u = 0).
Proof using.
intros b c u Hb Hc Hu. rewrite Z.lor_eq_0_iff, Z.land_lor_distr_l, Z.lor_eq_0_iff. tauto.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RAWADDX : rawadd_specX API.
Theorem ubs0_diff : diff_specX API.
Proof using IMG RAWADDX.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tv np S GPAL cur befr brb bc ha
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & HSV & W112 & W120 & W56 & W104 & G2 & G9 & G18 & G19 & G27 & G20 & G3 & G4)
HSINK HVALS R10 G14 W32 W16 G15 W24 Xha Xnp Xtv0 XG2 HNUM HRq.
set (gen1 := fl_gen3 (gcfg_of s GPAL) cur (Some befr)) in *.
pose proof HVALS as (_ & HVf & HVb & _). pose proof HVf as (XA1 & _). cbn [oframe_relb] in HVb. pose proof HVb as (XB1 & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (sp0 := spZ regs0) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in *. set (f1 := set_fr_gen f gen1) in *.
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (Hb1in : In (Some b) (cg_frames s1)).
{ rewrite Hfr1. eapply (nth_error_In _ (i - 1)). rewrite nth_error_list_set_other by lia. exact Hb. }
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg). destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
destruct (fl_img_geom0 API Lc Ac memc mdc g s N _ f HH0 HB Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW1 HH1; nia).
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj. pose proof (Hfrs b Hb1in) as Hbobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hbobj) as Rb.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rb 2%nat (fr_attr b) eq_refl) as Rbattr. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rbattr.
assert (M8 : forall fr, In (Some fr) (cg_frames s) -> fr_ptr fr mod 8 = 0).
{ intros fr Hfr.
pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fr) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; apply (frame_blocks_in_cgif0 g s N fr); [exact Hfr | left; reflexivity]) ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
pose proof (obj_at_range _ _ _ _ _ Hfobj 2%nat (fr_attr f) eq_refl) as Rfattr. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfattr.
pose proof (obj_at_range _ _ _ _ _ Hfobj 7%nat (fr_disp f) eq_refl) as Rdisp. cbn in Rdisp.
pose proof (land_le (fr_attr f) 4 ltac:(clear; lia)) as L4.
assert (Rha : 0 <= ha < 2 ^ 64) by (rewrite Xha; destruct (fl_hasAlpha (gcfg_of s GPAL) cur); clear; lia).
set (u := Z.land (fr_attr f) 1) in W56.
assert (Ru : 0 <= u <= 1) by (subst u; destruct (land1_cases (fr_attr f) ltac:(clear - Rfattr; lia)); lia).
set (E := Ereg regs1 (map (Z_to_bv 64) [fr_attr b; fr_img f; fr_ptr f; g; u; Z.land (fr_attr f) 4] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error [fr_attr b; fr_img f; fr_ptr f; g; u; Z.land (fr_attr f) 4] j = Some v -> ew E (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE32 : ew E 32 = Z_to_bv 64 (fr_attr b)) by (apply (HA 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (fr_img f)) by (apply (HA 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 (fr_ptr f)) by (apply (HA 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 g) by (apply (HA 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 u) by (apply (HA 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 (Z.land (fr_attr f) 4)) by (apply (HA 5%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr b) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hq0 Hq1 Hac HFRv; lia).
assert (HU34 : bv_unsigned (ew E 34) = fr_ptr f) by (rewrite HE34; apply unsigned_lit_small; clear - Hp0 Hp1 Hac HFRv; lia).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 272 72 88 dv_stk0)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold dv_stk0. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hg0 Hg1 Hac HGSv; lia | cbn; lia | apply val_mem_word_mem; exact W112].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hp0 Hp1 Hac HFRv; lia | cbn; lia | apply val_mem_word_mem; exact W120].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ru; lia | cbn; lia | apply val_mem_word_mem; exact W56].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_W s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - RW; lia | cbn; lia | apply val_mem_word_mem; exact W104].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_disp f)); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 14%nat 14%bv eq_refl), G14, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Rdisp; lia | cbn; lia | apply val_mem_word_mem; exact W32].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (Z.land (fr_attr f) 4)); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - L4; lia | cbn; lia | apply val_mem_word_mem; exact W16].
- eapply (chunk_ok_val _ _ _ _ _ _ _ ha); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 15%nat 15%bv eq_refl), G15, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Rha; lia | cbn; lia | apply val_mem_word_mem; exact W24]. }
assert (HR1 : region_ok ubs0segs E memc (YP09.mkRegion (Some 18%nat) 16 20 16 16 [mkChunk 16 (CVal 4 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [clear - Hq1 Hac HFRv; lia|]. split; [intros o Ho; lia|].
constructor; [| constructor]. eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_attr b)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by (clear - Rbattr; lia); reflexivity | cbn; clear - Rbattr; lia | cbn; lia |].
exact (proj1 (obj_at_nth ubs0segs memc (fr_ptr b) LAY_Frame (frame_vals b) 2 (16, 4%N) (fr_attr b) Hbobj eq_refl eq_refl)). }
assert (HR2 : region_ok ubs0segs E memc (YP09.mkRegion (Some 34%nat) 8 16 8 8 [mkChunk 8 (CVal 8 (SOff 33 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU34.
split; [lia|]. split; [clear - Hp1 Hac HFRv; lia|]. split; [intros o Ho; lia|].
constructor; [| constructor]. eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_img f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by (clear - Him0 Him1 Hac HN1; lia); reflexivity | cbn; clear - Him0 Him1 Hac HN1; lia | cbn; lia |].
exact (proj1 (obj_at_nth ubs0segs memc (fr_ptr f) LAY_Frame (frame_vals f1) 1 (8, 8%N) (fr_img f) Hfobj eq_refl eq_refl)). }
assert (HPD : pairwise_disjoint E (ss_mem ss_diff)).
{ pose proof (af_frames_sep0 API Lc Ac memc mdc g s N _ i (i - 1) f b HH0 HB Hf Hb ltac:(lia)) as Hfb.
cbn [ss_mem ss_diff pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18, HU34.
clear - Hp0 Hp1 Hq0 Hq1 Hfb Hceil HFSv HFRv Hac. repeat split; try exact I; lia. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (18%nat, mkAF 4096 CEIL_MAX 3); (34%nat, mkAF 4096 CEIL_MAX 3); (32%nat, mkAF 0 (2^32 - 1) 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU18, HU34, HE32, unsigned_lit_small by (clear - Rbattr; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (M8 f Hfin) as Hp8. pose proof (M8 b Hbin) as Hq8.
clear - Hceil Hsp063 Hal16 Hp0 Hp1 Hp8 Hq0 Hq1 Hq8 Rbattr HFSv HFRv Hac. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok ubs0segs E ss_diff (mkst regs1 (Z_to_bv 64 FL_DIFF) memc (seg_rom ubs0segs))).
{ unfold ss_diff. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]] | exact HPD | exact HFA]. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_DIFF) memc (seg_rom ubs0segs))) in HJ.
assert (WR : forall E0 cs rs blc, bv_unsigned (ew E0 2) = sp0 - 272 -> Forall (fun r => r_whi r <= r_wlo r) rs ->
wr_ok E0 (YP09.mkRegion (Some 2%nat) 0 272 72 88 cs :: rs) FLUSH_STK sp0 FP (blocks L A) blc).
{ intros E0 cs rs blc H2 Hrs. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
induction Hrs as [|r rs' Hr Hrs' IHrs]; [apply wr_ok_nil | apply wr_ok_cons_ro; [exact Hr | exact IHrs]]. }
assert (LEAF : forall ss ms' pc', st_ok ubs0segs E ss ms' -> ss_pc ss = pc' -> ss_resv ss = None ->
((pc' = FL_SLOW /\ YO07.flag (YO07.f_attr befr) 1 || YO07.flag (YO07.f_attr cur) 1 || YO07.flag (YO07.f_attr befr) 4 || YO07.flag (YO07.f_attr cur) 4 = true) \/
(pc' = FL_FAST /\ YO07.flag (YO07.f_attr befr) 1 = false /\ YO07.flag (YO07.f_attr cur) 1 = false /\ YO07.flag (YO07.f_attr befr) 4 = false /\ YO07.flag (YO07.f_attr cur) 4 = false)) ->
(exists rg0, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ incl_chunks dv_stk1 (r_chunks rg0) = true) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 18; 19; 20; 27]%bv = true ->
sr_get (ss_regs ss) 9%bv = SOff 33 0 ->
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 + 72 <= a < sp0 - 272 + 88) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
SR ubs0segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md)).
{ intros ss ms' pc' HS' Hpc Hrv Hpc' (rg0 & Hrg0 & Hb0 & Hincl) Hkl Q9 HJ' K'.
pose proof (regs_kept_of_st_ok ubs0segs _ ss ms' regs1 _ _ HS' (env_agree_refl _ _) Hkl) as R.
pose proof (st_region_chunks ubs0segs E ss ms' 0 rg0 2%nat (sp0 - 272) HS' Hrg0 Hb0 HU2) as Hcs.
apply incl_chunks_sound in Hincl.
assert (CW : forall off e val, In (mkChunk off (CVal 8 e)) dv_stk1 -> sv_denot E e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> word_mem ubs0segs (ms_mem ms') (sp0 - 272 + off) val)
by (intros off e val Hin He Hval; exact (chunk_word E _ _ off _ _ (proj1 (Forall_forall _ _) Hcs _ (Hincl _ Hin)) He Hval)).
assert (KB : forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs (ms_mem ms') (bb + k) = mbyte ubs0segs memc (bb + k)).
{ intros bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0' R1']. apply K'; clear - R0' R1' Hk Hceil HFSv Hac; lia. }
assert (PRE : dv_pre API L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b gen1 rest FP tv np (fr_disp f) (Z.land (fr_attr f) 4) ha).
{ split; [exact HJ'|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ split; [| split].
- rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]].
- change (cg_raw (flush_upd s i gen1 (rw_cur s))) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KB (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia]].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif0 g s N f _ _ Hfin). left. reflexivity.
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif0 g s N x _ _ Hin). left. reflexivity. }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact Hb|]. split; [exact HFP|]. split; [exact HB|].
split; [exact Htv|]. split; [exact Hnp|]. split; [clear - Rdisp; lia|]. split; [clear - L4; lia|]. split; [exact Rha|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K'; clear - Ha Hceil Hsp063 HFSv Hac; lia]|].
split; [apply (CW 112 (SOff 35 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity | clear - Hg0 Hg1 Hac HGSv; lia]|].
split; [apply (CW 120 (SOff 34 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity | clear - Hp0 Hp1 Hac HFRv; lia]|].
split; [apply (CW 72 (SOff 9 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), G9, Z_to_bv_bv_unsigned; reflexivity | exact Htv]|].
split; [apply (CW 80 (SOff 19 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), G19, Z_to_bv_bv_unsigned; reflexivity | clear - RH; lia]|].
split; [apply (CW 104 (SOff 27 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity | clear - RW; lia]|].
split; [apply (CW 56 (SOff 36 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned; reflexivity | clear - Ru; lia]|].
split; [apply (CW 32 (SOff 14 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, (HE 14%nat 14%bv eq_refl), G14, Z_to_bv_bv_unsigned; reflexivity | clear - Rdisp; lia]|].
split; [apply (CW 16 (SOff 37 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned; reflexivity | clear - L4; lia]|].
split; [apply (CW 24 (SOff 15 0)); [unfold dv_stk1; repeat (first [left; reflexivity | right]) | cbn [sv_denot]; rewrite Z.add_0_r, (HE 15%nat 15%bv eq_refl), G15, Z_to_bv_bv_unsigned; reflexivity | exact Rha]|].
split; [rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2|].
split; [rewrite (st_ok_reg ubs0segs E ss ms' 9%bv HS'), Q9; cbn [sv_denot]; rewrite Z.add_0_r, HE33, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (R 18%bv ltac:(cbv; auto 50)); exact G18|]. split; [rewrite (R 27%bv ltac:(cbv; auto 50)); exact G27|].
split; [rewrite (R 20%bv ltac:(cbv; auto 50)); exact G20|]. split; [rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19|].
split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4]. }
assert (HVALS' : fl_vals (ms_mem ms') s N f (Some b) GPAL cur (Some befr)).
{ eapply fl_vals_kept; [| exact HVALS]. intros a0 n0 k Hin Hk. apply (KB a0 n0 k); [| exact Hk].
exact (fl_vblocks_sub g s N f (Some b) i Hf ltac:(right; exists (i - 1)%nat; exact Hb) _ Hin). }
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc. destruct Hpc' as [[-> Hslow] | (-> & F1 & F2 & F3 & F4)].
- exact (fl_slow API IMG RAWADDX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b rest FP FPw tv np (fr_disp f) (Z.land (fr_attr f) 4) ha S GPAL cur befr brb bc PRE
HSINK HVALS' eq_refl eq_refl Xha Xnp Xtv0 XG2 HNUM HRq Hslow).
- exact (fl_fast API IMG RAWADDX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b rest FP FPw tv np (fr_disp f) (Z.land (fr_attr f) 4) ha S GPAL cur befr brb bc PRE
HSINK HVALS' eq_refl eq_refl Xha Xnp Xtv0 XG2 HNUM HRq F1 F2 F3 F4). }
assert (KOF : forall (m m' : word -> option byte) E0 rs rs1 rs2, bv_unsigned (ew E0 2) = sp0 - 272 ->
frame_of E0 (YP09.mkRegion (Some 2%nat) 0 272 72 88 rs :: YP09.mkRegion (Some 18%nat) 16 20 16 16 rs1 :: YP09.mkRegion (Some 34%nat) 8 16 8 8 rs2 :: nil) m m' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 + 72 <= a < sp0 - 272 + 88) -> mbyte ubs0segs m a = mbyte ubs0segs memc a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 + 72 <= a < sp0 - 272 + 88) -> mbyte ubs0segs m' a = mbyte ubs0segs memc a).
{ intros m m' E0 rs rs1 rs2 H2 HFx K a Ha Hna. rewrite <- (K a Ha Hna). apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [r_base r_wlo r_whi base_val]; rewrite ?H2; clear - Hna; lia. }
jrun LAWS ubs0tbl_ok HS HJ. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF.
pose proof (KOF _ _ _ _ _ _ HU2 HF ltac:(intros a _ _; reflexivity)) as K1. clear HF HG.
assert (HU32 : U E (SOff 32 0) = fr_attr b) by (apply (U_atom _ 32 (fr_attr b) HE32); clear - Rbattr; lia).
assert (HU36 : U E (SOff 36 0) = u) by (apply (U_atom _ 36 u HE36); clear - Ru; lia).
assert (HU10 : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 10 0) (SLit 32)) (SLit 32)) = fr_attr f).
{ rewrite U_zext32_shifts_mod_d, (U_atom E 10 (bv_unsigned (getr regs1 10)) ltac:(rewrite (HE 10%nat 10%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned) (u64_range_getr regs1 10)). exact R10. }
assert (C1 : U E (SAlu ALU_AND (SOff 32 0) (SLit 1)) = Z.land (fr_attr b) 1) by (rewrite U_and_lit, HU32 by (clear; lia); reflexivity).
assert (C2 : U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_OR (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 10 0) (SLit 32)) (SLit 32))) (SLit 4)) (SOff 36 0))
= Z.lor (Z.land (Z.lor (fr_attr b) (fr_attr f)) 4) u) by (rewrite U_or_d, U_and_lit, U_or_d, HU32, HU10, HU36 by (clear; lia); reflexivity).
assert (FL : forall a m, (Z.land a m =? 0) = negb (YO07.flag a m)) by (intros; unfold YO07.flag; rewrite Bool.negb_involutive; reflexivity).
jbranch ubs0tbl HS.
-
rewrite branch_ne_U, C1, U_lit, XB1, FL in Hc by (clear; lia).
jrun_to LAWS ubs0tbl_ok HS HJ FL_SLOW. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF. pose proof (KOF _ _ _ _ _ _ HU2 HF K1) as K2. clear HF HG.
apply (LEAF _ _ FL_SLOW HS eq_refl eq_refl); [left; split; [reflexivity | destruct (YO07.flag (YO07.f_attr befr) 1); [reflexivity | discriminate Hc]] | | vm_compute; reflexivity | reflexivity | exact HJ | exact K2].
eexists. split; [reflexivity|]. split; [reflexivity|]. vm_compute; reflexivity.
- rewrite branch_ne_U, C1, U_lit, XB1, FL in Hc by (clear; lia). rename Hc into Hc1.
jrun LAWS ubs0tbl_ok HS HJ. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF. pose proof (KOF _ _ _ _ _ _ HU2 HF K1) as K2. clear HF HG.
jbranch ubs0tbl HS.
+
rewrite branch_eq_U, C2, U_lit in Hc by (clear; lia). apply Z.eqb_eq in Hc.
apply (lor_land4_zero (fr_attr b) (fr_attr f) u ltac:(clear - Rbattr; lia) ltac:(clear - Rfattr; lia) Ru) in Hc as (Hb4 & Hf4 & Hu0).
jrun_to LAWS ubs0tbl_ok HS HJ FL_FAST. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF. pose proof (KOF _ _ _ _ _ _ HU2 HF K2) as K3. clear HF HG.
apply (LEAF _ _ FL_FAST HS eq_refl eq_refl); [| | vm_compute; reflexivity | reflexivity | exact HJ | exact K3].
{ right. split; [reflexivity|]. split; [destruct (YO07.flag (YO07.f_attr befr) 1); [discriminate Hc1 | reflexivity] |].
unfold YO07.flag. rewrite <- XB1, <- XA1, Hb4, Hf4. unfold u in Hu0. rewrite Hu0. repeat split; reflexivity. }
eexists. split; [reflexivity|]. split; [reflexivity|]. vm_compute; reflexivity.
+ rewrite branch_eq_U, C2, U_lit in Hc by (clear; lia).
jrun_to LAWS ubs0tbl_ok HS HJ FL_SLOW. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF. pose proof (KOF _ _ _ _ _ _ HU2 HF K2) as K3. clear HF HG.
apply (LEAF _ _ FL_SLOW HS eq_refl eq_refl); [| | vm_compute; reflexivity | reflexivity | exact HJ | exact K3].
{ left. split; [reflexivity|]. unfold YO07.flag. rewrite <- XB1, <- XA1.
destruct (Z.eqb_spec (Z.land (fr_attr b) 4) 0) as [Hb4|Hb4]; [| destruct (Z.land (fr_attr b) 1 =? 0), (Z.land (fr_attr f) 1 =? 0); reflexivity].
destruct (Z.eqb_spec (Z.land (fr_attr f) 4) 0) as [Hf4|Hf4]; [| destruct (Z.land (fr_attr b) 1 =? 0), (Z.land (fr_attr f) 1 =? 0); reflexivity].
destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0) as [Hf1|Hf1]; [| destruct (Z.land (fr_attr b) 1 =? 0); reflexivity].
exfalso. destruct (Z.eqb_spec (Z.lor (Z.land (Z.lor (fr_attr b) (fr_attr f)) 4) u) 0) as [Hz|Hz]; [discriminate Hc|].
apply Hz. apply (proj2 (lor_land4_zero (fr_attr b) (fr_attr f) u ltac:(clear - Rbattr; lia) ltac:(clear - Rfattr; lia) Ru)).
split; [exact Hb4|]. split; [exact Hf4|]. unfold u. exact Hf1. }
eexists. split; [reflexivity|]. split; [reflexivity|]. vm_compute; reflexivity.
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
