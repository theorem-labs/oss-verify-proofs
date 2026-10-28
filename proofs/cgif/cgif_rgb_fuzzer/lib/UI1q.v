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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l UO3m YI00 YI02 YI01 YI03
UI1e UI1c UI39 UI1i UI20 UI2r UI59 UI56 YI0x UI57
UI1h UI16 UI1z UI1k UI21 UI22
UI23 UI24 UI1x UI1w UI1j UI1v UI1p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_diff : sstate :=
mkSS FL_DIFF sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 272 72 88 [mkChunk 120 (CVal 8 (SOff 32 0)); mkChunk 56 (CVal 8 (SOff 35 0))] ;
YQ0b.mkRegion (Some 18%nat) 16 20 16 16 [mkChunk 16 (CVal 4 (SOff 33 0))] ;
YQ0b.mkRegion (Some 32%nat) 8 16 8 8 [mkChunk 8 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (18%nat, mkAF 4096 CEIL_MAX 3); (32%nat, mkAF 4096 CEIL_MAX 3); (33%nat, mkAF 0 4294967295 0) ] [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Theorem ubs2_diff : diff_spec API.
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & HSV & W112 & W120 & W104 & W56 &
(u23 & u24 & u25 & R23 & R24 & R25 & W32 & W16 & W24) & G2 & G9 & G18 & G19 & G20 & G10 & G3 & G4).
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
destruct (af_cgif_geom API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg). destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
destruct (fl_img_geom API Lc Ac memc mdc g s N _ f HH0 HB Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW1 HH1; nia).
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj. pose proof (Hfrs b Hb1in) as Hbobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hbobj) as Rb.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rb 2%nat (fr_attr b) eq_refl) as Rbattr. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rbattr.
assert (M8 : forall fr, In (Some fr) (cg_frames s) -> fr_ptr fr mod 8 = 0).
{ intros fr Hfr.
pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fr) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; apply (frame_blocks_in_cgif g s N fr); [exact Hfr | left; reflexivity]) ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
set (u := Z.land (fr_attr f) 1) in W56.
pose proof (obj_at_range _ _ _ _ _ Hfobj 2%nat (fr_attr f) eq_refl) as Rfattr. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfattr.
assert (Ru : 0 <= u <= 1) by (subst u; destruct (land1_cases (fr_attr f) ltac:(clear - Rfattr; lia)); lia).
set (E := Ereg regs1 (map (Z_to_bv 64) [fr_ptr f; fr_attr b; fr_img f; u] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fr_ptr f)) by (subst E; apply (Ereg_vals regs1 [fr_ptr f; fr_attr b; fr_img f; u] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (fr_attr b)) by (subst E; apply (Ereg_vals regs1 [fr_ptr f; fr_attr b; fr_img f; u] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 (fr_img f)) by (subst E; apply (Ereg_vals regs1 [fr_ptr f; fr_attr b; fr_img f; u] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 u) by (subst E; apply (Ereg_vals regs1 [fr_ptr f; fr_attr b; fr_img f; u] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr b) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hq0 Hq1 Hac HFRv; lia).
assert (HU32 : bv_unsigned (ew E 32) = fr_ptr f) by (rewrite HE32; apply unsigned_lit_small; clear - Hp0 Hp1 Hac HFRv; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 272 72 88 [mkChunk 120 (CVal 8 (SOff 32 0)); mkChunk 56 (CVal 8 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
constructor; [| constructor; [| constructor]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hp0 Hp1 Hac HFRv; lia | cbn; lia | apply val_mem_word_mem; exact W120].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ru; lia | cbn; lia | apply val_mem_word_mem; exact W56]. }
assert (HR1 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 18%nat) 16 20 16 16 [mkChunk 16 (CVal 4 (SOff 33 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [clear - Hq1 Hac HFRv; lia|]. split; [intros o Ho; lia|].
constructor; [| constructor]. eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_attr b)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by (clear - Rbattr; lia); reflexivity | cbn; clear - Rbattr; lia | cbn; lia |].
exact (proj1 (obj_at_nth ubs2segs memc (fr_ptr b) LAY_Frame (frame_vals b) 2 (16, 4%N) (fr_attr b) Hbobj eq_refl eq_refl)). }
assert (HR2 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 32%nat) 8 16 8 8 [mkChunk 8 (CVal 8 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [clear - Hp1 Hac HFRv; lia|]. split; [intros o Ho; lia|].
constructor; [| constructor]. eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_img f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by (clear - Him0 Him1 Hac HN1; lia); reflexivity | cbn; clear - Him0 Him1 Hac HN1; lia | cbn; lia |].
exact (proj1 (obj_at_nth ubs2segs memc (fr_ptr f) LAY_Frame (frame_vals f1) 1 (8, 8%N) (fr_img f) Hfobj eq_refl eq_refl)). }
assert (HPD : pairwise_disjoint E (ss_mem ss_diff)).
{ pose proof (af_frames_sep API Lc Ac memc mdc g s N _ i (i - 1) f b HH0 HB Hf Hb ltac:(lia)) as Hfb.
cbn [ss_mem ss_diff pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18, HU32.
clear - Hp0 Hp1 Hq0 Hq1 Hfb Hceil HFSv HFRv Hac. repeat split; try exact I; lia. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (18%nat, mkAF 4096 CEIL_MAX 3); (32%nat, mkAF 4096 CEIL_MAX 3); (33%nat, mkAF 0 4294967295 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU18, HU32, HE33, unsigned_lit_small by (clear - Rbattr; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (M8 f Hfin) as Hp8. pose proof (M8 b Hbin) as Hq8.
clear - Hceil Hsp063 Hal16 Hp0 Hp1 Hp8 Hq0 Hq1 Hq8 Rbattr HFSv HFRv Hac. repeat split; try lia.
replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok ubs2segs E ss_diff (mkst regs1 (Z_to_bv 64 FL_DIFF) memc (seg_rom ubs2segs))).
{ unfold ss_diff. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]] | exact HPD | exact HFA]. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_DIFF) memc (seg_rom ubs2segs))) in HJ.
assert (WR : forall E0 cs rs blc, bv_unsigned (ew E0 2) = sp0 - 272 -> Forall (fun r => r_whi r <= r_wlo r) rs ->
wr_ok E0 (YQ0b.mkRegion (Some 2%nat) 0 272 72 88 cs :: rs) FLUSH_STK sp0 FP (blocks L A) blc).
{ intros E0 cs rs blc H2 Hrs. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
induction Hrs as [|r rs' Hr Hrs' IHrs]; [apply wr_ok_nil | apply wr_ok_cons_ro; [exact Hr | exact IHrs]]. }
assert (LEAF : forall ss ms' pc', st_ok ubs2segs E ss ms' -> ss_pc ss = pc' -> ss_resv ss = None -> (pc' = FL_SLOW \/ pc' = FL_FAST) ->
(exists rg0, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\
In (mkChunk 72 (CVal 8 (SOff 9 0))) (r_chunks rg0) /\ In (mkChunk 80 (CVal 8 (SOff 19 0))) (r_chunks rg0)) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 18; 19; 20]%bv = true ->
sr_get (ss_regs ss) 9%bv = SOff 34 0 ->
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 + 72 <= a < sp0 - 272 + 88) -> mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
SR ubs2segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FP L A mem md)).
{ intros ss ms' pc' HS' Hpc Hrv Hpc' (rg0 & Hrg0 & Hb0 & I72 & I80) Hkl Q9 HJ' K'.
pose proof (regs_kept_of_st_ok ubs2segs _ ss ms' regs1 _ _ HS' (env_agree_refl _ _) Hkl) as R.
pose proof (st_region_chunks ubs2segs E ss ms' 0 rg0 2%nat (sp0 - 272) HS' Hrg0 Hb0 HU2) as Hcs.
assert (CW : forall off e val, In (mkChunk off (CVal 8 e)) (r_chunks rg0) -> sv_denot E e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> word_mem ubs2segs (ms_mem ms') (sp0 - 272 + off) val)
by (intros off e val Hin He Hval; exact (chunk_word E _ _ off _ _ (proj1 (Forall_forall _ _) Hcs _ Hin) He Hval)).
assert (WK : forall off v, 0 <= off -> off + 8 <= 72 \/ 88 <= off -> off + 8 <= 272 -> word_mem ubs2segs memc (sp0 - 272 + off) v -> word_mem ubs2segs (ms_mem ms') (sp0 - 272 + off) v).
{ intros off v H0 H1 H2 W k Hk. rewrite K'; [exact (W k Hk) | clear - H0 H2 Hk Hceil Hsp063 HFSv Hac; lia | clear - H1 Hk; lia]. }
assert (KB : forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> mbyte ubs2segs (ms_mem ms') (bb + k) = mbyte ubs2segs memc (bb + k)).
{ intros bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0' R1']. apply K'; clear - R0' R1' Hk Hceil HFSv Hac; lia. }
assert (PRE : dv_pre API L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b gen1 rest FP tv np u23 u24 u25).
{ split; [exact HJ'|]. split; [exact Hid|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split.
{ split; [| split].
- rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]].
- change (cg_raw (flush_upd s i gen1 (rw_cur s))) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KB (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia]].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N f _ _ Hfin). left. reflexivity.
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif g s N x _ _ Hin). left. reflexivity. }
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact Hb|]. split; [exact HFP|]. split; [exact HB|].
split; [exact Htv|]. split; [exact Hnp|]. split; [exact R23|]. split; [exact R24|]. split; [exact R25|].
split; [apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K'; clear - Ha Hceil Hsp063 HFSv Hac; lia]|].
split; [exact (WK 112 g ltac:(lia) ltac:(lia) ltac:(lia) W112)|].
split; [exact (WK 120 (fr_ptr f) ltac:(lia) ltac:(lia) ltac:(lia) W120)|].
split; [apply (CW 72 (SOff 9 0) _ I72); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), G9, Z_to_bv_bv_unsigned; reflexivity | exact Htv]|].
split; [apply (CW 80 (SOff 19 0) _ I80); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), G19, Z_to_bv_bv_unsigned; reflexivity | clear - RH; lia]|].
split; [exact (WK 104 (cg_W s) ltac:(lia) ltac:(lia) ltac:(lia) W104)|].
split; [exact (WK 56 u ltac:(lia) ltac:(lia) ltac:(lia) W56)|].
split; [exact (WK 32 u23 ltac:(lia) ltac:(lia) ltac:(lia) W32)|].
split; [exact (WK 16 u24 ltac:(lia) ltac:(lia) ltac:(lia) W16)|].
split; [exact (WK 24 u25 ltac:(lia) ltac:(lia) ltac:(lia) W24)|].
split; [rewrite (R 2%bv ltac:(cbv; auto 50)); exact G2|].
split; [rewrite (st_ok_reg ubs2segs E ss ms' 9%bv HS'), Q9; cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (R 18%bv ltac:(cbv; auto 50)); exact G18|]. split; [rewrite (R 19%bv ltac:(cbv; auto 50)); exact G19|].
split; [rewrite (R 20%bv ltac:(cbv; auto 50)); exact G20|].
split; [rewrite (R 3%bv ltac:(cbv; auto 50)); exact G3 | rewrite (R 4%bv ltac:(cbv; auto 50)); exact G4]. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc. destruct Hpc' as [-> | ->].
- exact (fl_slow API IMG RAWADD L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE).
- exact (fl_fast API IMG RAWADD L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f b gen1 rest FP tv np u23 u24 u25 PRE). }
assert (KOF : forall (m m' : word -> option byte) E0 rs, bv_unsigned (ew E0 2) = sp0 - 272 ->
frame_of E0 (YQ0b.mkRegion (Some 2%nat) 0 272 72 88 rs :: YQ0b.mkRegion (Some 18%nat) 16 20 16 16 [mkChunk 16 (CVal 4 (SOff 33 0))] :: YQ0b.mkRegion (Some 32%nat) 8 16 8 8 [mkChunk 8 (CVal 8 (SOff 34 0))] :: nil) m m' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 + 72 <= a < sp0 - 272 + 88) -> mbyte ubs2segs m a = mbyte ubs2segs memc a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 + 72 <= a < sp0 - 272 + 88) -> mbyte ubs2segs m' a = mbyte ubs2segs memc a).
{ intros m m' E0 rs H2 HFx K a Ha Hna. rewrite <- (K a Ha Hna). apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [r_base r_wlo r_whi base_val]; rewrite ?H2; clear - Hna; lia. }
jrun LAWS ubs2tbl_ok HS HJ. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF.
pose proof (KOF _ _ _ _ HU2 HF ltac:(intros a _ _; reflexivity)) as K1. clear HF HG.
jbranch ubs2tbl HS.
-
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ FL_SLOW. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF. pose proof (KOF _ _ _ _ HU2 HF K1) as K2. clear HF HG.
apply (LEAF _ _ FL_SLOW HS eq_refl eq_refl ltac:(left; reflexivity)); [| vm_compute; reflexivity | reflexivity | exact HJ | exact K2].
eexists. split; [reflexivity|]. split; [reflexivity|]. cbn [r_chunks In]. repeat split; tauto.
- clear Hc. jrun LAWS ubs2tbl_ok HS HJ. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF. pose proof (KOF _ _ _ _ HU2 HF K1) as K2. clear HF HG.
jbranch ubs2tbl HS.
+
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ FL_FAST. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF. pose proof (KOF _ _ _ _ HU2 HF K2) as K3. clear HF HG.
apply (LEAF _ _ FL_FAST HS eq_refl eq_refl ltac:(right; reflexivity)); [| vm_compute; reflexivity | reflexivity | exact HJ | exact K3].
eexists. split; [reflexivity|]. split; [reflexivity|]. cbn [r_chunks In]. repeat split; tauto.
+ clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ FL_SLOW. { apply WR; [exact HU2 | constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]. }
cbn [ms_mem mkst] in HF. pose proof (KOF _ _ _ _ HU2 HF K2) as K3. clear HF HG.
apply (LEAF _ _ FL_SLOW HS eq_refl eq_refl ltac:(left; reflexivity)); [| vm_compute; reflexivity | reflexivity | exact HJ | exact K3].
eexists. split; [reflexivity|]. split; [reflexivity|]. cbn [r_chunks In]. repeat split; tauto.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
