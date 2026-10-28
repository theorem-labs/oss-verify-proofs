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
UI1h UI16 UI1z UI1k UI21 UI22 UI23 UI24 UI1x.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition fl_entry_chunks : list YQ0b.chunk :=
[ mkChunk (-8) (CVal 8 (SOff 1 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-32) (CVal 8 (SOff 18 0));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-64) (CVal 8 (SOff 22 0));
mkChunk (-72) (CVal 8 (SOff 23 0)); mkChunk (-80) (CVal 8 (SOff 24 0)); mkChunk (-88) (CVal 8 (SOff 25 0)); mkChunk (-96) (CVal 8 (SOff 26 0));
mkChunk (-104) (CVal 8 (SOff 27 0)) ].
Lemma fl_saved_word : forall E mem sp0 off n (regs : bvmap 5 word) (rr : reg),
chunk_ok ubs2segs E mem sp0 (mkChunk off (CVal 8 (SOff n 0))) -> ew E n = getr regs rr ->
forall a, a = sp0 + off -> word_mem ubs2segs mem a (bv_unsigned (getr regs rr)).
Proof.
intros E mem sp0 off n regs rr Hc He a ->. apply val_mem_word_mem.
eapply (val_of_chunk_ok ubs2segs E mem sp0 off 8%N (SOff n 0)); [exact Hc | | cbn; apply u64_range_getr | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, He, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma fl_saved_of_entry : forall E (regs : bvmap 5 word) mem sp0 cs,
Forall (chunk_ok ubs2segs E mem sp0) cs ->
(forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
incl fl_entry_chunks cs ->
fl_saved_ok mem sp0 regs.
Proof.
intros E regs mem sp0 cs Hcs HE Hincl j r Hr.
assert (Hj : (j < 13)%nat) by (apply (proj1 (nth_error_Some FL_SAVED j)); rewrite Hr; discriminate).
assert (Hc : chunk_ok ubs2segs E mem sp0 (nth j fl_entry_chunks (mkChunk 0 (CVal 8 (SLit 0))))).
{ apply (proj1 (Forall_forall _ _) Hcs). apply Hincl. apply nth_In. cbn. exact Hj. }
do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; cbn [nth fl_entry_chunks] in Hc;
eapply (fl_saved_word E mem sp0 _ _ regs _ Hc); [apply HE; reflexivity | cbn; lia] |]).
cbn in Hj. lia.
Qed.
Definition ss_e (pz : bool) : sstate :=
mkSS ubs2_A_flushFrame (if pz then sr_set sr_atoms 12%bv (SLit 0) else sr_atoms)
[ YQ0b.mkRegion (Some 2%nat) (-272) 0 (-272) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG) ;
YQ0b.mkRegion (Some 11%nat) 0 40 20 24 (obj_chunks_gen LAY_Frame A_F []) ] None
(mkFacts ([(2%nat, mkAF (CEIL_MIN + FLUSH_STK) (2^63 - 1) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4); (11%nat, mkAF 4096 (CEIL_MAX - 40) 3)]
++ (if pz then [] else [(12%nat, mkAF 4096 CEIL_MAX 0)]) ++ fl_gfacts ++ fl_ffacts) [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis RAWADD : rawadd_spec API.
Hypothesis DIFF : diff_spec API.
Theorem ubs2_flushFrame : flush_spec API.
Proof.
intros L A regs mem md g s N i f rest HPRE Hid G10 Hat Hwf Hi Hf G11 G12 HB.
pose proof HPRE as (HH & Hra0 & Hst & Htp0 & Herr). destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
set (sp0 := spZ regs) in *.
set (FP := blocks_fp (cgif_blocks g s N)).
assert (HFP : forall b' n a, In (b', n) (cgif_blocks g s N) -> b' <= a < b' + n -> inFP FP a) by (intros b' n a Hbn Ha; apply (cgif_fp_in g s N b' n a Hbn Ha)).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
destruct (af_cgif_geom API L A mem md g s N _ HH HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg).
destruct (fl_img_geom API L A mem md g s N _ f HH HB Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof (Hfrs f Hfin) as Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr. pose proof (Rf 3%nat (fr_gen f) eq_refl) as Rfgen. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfattr, Rfgen.
assert (Hfblk : In (fr_ptr f, FRAME_SIZE) (blocks L A)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. apply (frame_blocks_in_cgif g s N f); [exact Hfin | left; reflexivity]. }
assert (Hp8 : fr_ptr f mod 8 = 0).
{ pose proof (heap_blocks_range _ _ LAWS L A mem md (fr_ptr f) FRAME_SIZE HH Hfblk ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
set (E := fl_E regs regs s f None []).
pose proof (fl_HE regs regs s f None [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HX regs regs s f None [] : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (fl_HF regs regs s f None [] : forall n j v, _ -> _ -> ew E n = _) as HFf.
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = g) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Hg0 Hg1 Hac HGSv; lia).
assert (HU11 : bv_unsigned (ew E 11) = fr_ptr f) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; clear - Hp0 Hp1 Hac HFRv; lia).
assert (HE64 : ew E 64 = Z_to_bv 64 (fr_attr f)) by (apply (HFf 64%nat 2%nat _ eq_refl eq_refl)).
assert (HE65 : ew E 65 = Z_to_bv 64 (fr_gen f)) by (apply (HFf 65%nat 3%nat _ eq_refl eq_refl)).
assert (V10 : U E (SExt true 32 (SOff 64 0)) mod 2 ^ 32 = fr_attr f) by (apply (U_sext32_low E 64 (fr_attr f) HE64); clear - Rfattr; lia).
assert (HR0 : region_ok ubs2segs E mem (YQ0b.mkRegion (Some 2%nat) (-272) 0 (-272) 0 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil]. }
assert (HR1 : region_ok ubs2segs E mem (YQ0b.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG))).
{ unfold fl_litsG, A_X. eapply (region_ok_obj_gen ubs2segs E mem 10 g 96 0 0 LAY_CGIF (cgif_vals s) 45 (litsG None None None None));
[exact HU10 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros k Hk; lia].
intros j v Hj. apply (HX (45 + j)%nat j v eq_refl Hj). }
assert (HR2 : region_ok ubs2segs E mem (YQ0b.mkRegion (Some 11%nat) 0 40 20 24 (obj_chunks_gen LAY_Frame A_F []))).
{ unfold A_F. eapply (region_ok_obj_gen ubs2segs E mem 11 (fr_ptr f) 40 20 24 LAY_Frame (frame_vals f) 62 []);
[exact HU11 | lia | lia | exact Hfobj | reflexivity | | intros [|j] z Hz; discriminate Hz | ].
- intros j v Hj. apply (HFf (62 + j)%nat j v eq_refl Hj).
- intros k Hk. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L A mem md (fr_ptr f) FRAME_SIZE k HH Hfblk ltac:(clear - Hk HFRv; lia))). }
assert (HPD : forall pz, pairwise_disjoint E (ss_mem (ss_e pz))).
{ intros pz. cbn [ss_mem ss_e pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11. clear - Hg1 Hp1 Hpg Hceil HFSv HGSv HFRv Hac. repeat split; lia. }
pose proof (fl_gfacts_ok regs regs s f None [] mem g N Hobj Hwf ltac:(lia) ltac:(lia)) as HFAb.
pose proof (fl_ffacts_ok regs regs s f None [] mem (fr_ptr f) Hfobj Him0 ltac:(clear - Him1 HN HW1 HH1; nia)) as HFAc.
assert (HFAa : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK) (2^63 - 1) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4); (11%nat, mkAF 4096 (CEIL_MAX - 40) 3)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. clear - Hceil H63 Hal16 Hg0 Hg1 Hg16 Hp0 Hp1 Hp8 HFSv HGSv HFRv Hac. repeat split; lia. }
assert (HFAd : frame_ptr (nth (i - 1) (cg_frames s) None) <> 0 -> atoms_ok E [(12%nat, mkAF 4096 CEIL_MAX 0)]).
{ intros Hnz. destruct (nth (i - 1) (cg_frames s) None) as [b|] eqn:Hn; [| exfalso; apply Hnz; reflexivity].
assert (Hbin : In (Some b) (cg_frames s)) by (rewrite <- Hn; apply nth_In; lia).
destruct (Hfgeom b Hbin) as (Q0 & Q1 & _).
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE 12%nat 12%bv eq_refl), G12; try rewrite Hn. cbn [frame_ptr]. rewrite unsigned_lit_small by (clear - Q0 Q1 Hac HFRv; lia).
change (2 ^ 0) with 1. rewrite Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Q0 Q1 HFRv. repeat split; lia. }
assert (MK : forall pz : bool, (if pz then frame_ptr (nth (i - 1) (cg_frames s) None) = 0 else frame_ptr (nth (i - 1) (cg_frames s) None) <> 0) ->
st_ok ubs2segs E (ss_e pz) (mkst regs (Z_to_bv 64 ubs2_A_flushFrame) mem (seg_rom ubs2segs))).
{ intros pz Hpz. unfold ss_e. apply entry_st_ok_full; [| vm_compute; destruct pz; reflexivity | | exact (HPD pz) |].
- destruct pz; [| apply regs_ok_Ereg]. apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite G12, Hpz. reflexivity.
- constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor.
- split; [| split; exact I]. apply atoms_ok_app; [exact HFAa|]. apply atoms_ok_app; [| apply atoms_ok_app; [exact HFAb | exact HFAc]].
destruct pz; [exact I | exact (HFAd Hpz)]. }
clear HR0 HR1 HR2 HPD HFAa HFAb HFAc HFAd.
pose proof (journal_init ubs2_msyms MR FLUSH_STK FP L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_flushFrame) mem (seg_rom ubs2segs))) in HJ. fold sp0 in HJ.
assert (WR : forall E0 cs fcs, bv_unsigned (ew E0 2) = sp0 -> bv_unsigned (ew E0 11) = fr_ptr f ->
wr_ok E0 [YQ0b.mkRegion (Some 2%nat) (-272) 0 (-272) 0 cs; YQ0b.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG);
YQ0b.mkRegion (Some 11%nat) 0 40 20 24 fcs] FLUSH_STK sp0 FP (blocks L A) (blocks L A)).
{ intros E0 cs fcs H2 H11. eapply wr_ok_cons_stack; [reflexivity | exact H2 | cbn; lia | cbn; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_block E0 (YQ0b.mkRegion (Some 11%nat) 0 40 20 24 fcs) [] FLUSH_STK sp0 FP (blocks L A) (blocks L A) 11 (fr_ptr f) FRAME_SIZE eq_refl H11 Hfblk); [cbn; lia | cbn; clear - HFRv; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. apply (HFP (fr_ptr f) FRAME_SIZE a); [| clear - Ha HFRv; lia].
apply (frame_blocks_in_cgif g s N f _ _ Hfin). left. reflexivity. }
assert (KSTEP : forall E0 cs fcs (m m' : word -> option byte),
bv_unsigned (ew E0 2) = sp0 -> bv_unsigned (ew E0 11) = fr_ptr f ->
frame_of E0 [YQ0b.mkRegion (Some 2%nat) (-272) 0 (-272) 0 cs; YQ0b.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG);
YQ0b.mkRegion (Some 11%nat) 0 40 20 24 fcs] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs2segs m' a = mbyte ubs2segs m a).
{ intros E0 cs fcs m m' H2 H11 HFx a Ha Hn1 Hn2. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?H2, ?H11; clear - Hn1 Hn2; lia |]). destruct Hr. }
assert (FRo : forall x j v rcur, nth_error (cg_frames s) j = Some (Some x) -> j <> i -> In (Some x) (cg_frames (flush_upd s i v rcur))).
{ intros x j v rcur Hj Hji. rewrite (cg_frames_flush_upd s i v rcur f Hf). eapply (nth_error_In _ j). rewrite nth_error_list_set_other by lia. exact Hj. }
assert (CGAT : forall (m : word -> option byte) (v : Z),
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs2segs m a = mbyte ubs2segs mem a) ->
field_ok ubs2segs m (fr_ptr f) (20, 4%N) v ->
cgif_at m g (flush_upd s i v (rw_cur s))).
{ intros m v K Hfld.
assert (KB : forall bb nn k, In (bb, nn) (cgif_blocks g s N) -> 0 <= k < nn -> (bb + nn <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= bb) ->
mbyte ubs2segs m (bb + k) = mbyte ubs2segs mem (bb + k)).
{ intros bb nn k Hbn Hk Hsep. assert (Hbn' : In (bb, nn) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS L A mem md bb nn HH Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hsep Hceil HFSv HFRv Hac; lia. }
split; [| split].
- rewrite (cgif_vals_flush_upd s i v (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia | clear - Hpg; lia]].
- change (cg_raw (flush_upd s i v (rw_cur s))) with (cg_raw s). change (raw_vals g (flush_upd s i v (rw_cur s))) with (raw_vals g s).
pose proof (af_raw_frame_sep API L A mem md g s N _ f HH HB Hfin) as Hrf.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KB (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia | clear - Hrf; lia]].
- intros x Hx. destruct (In_frames_flush_upd s i v (rw_cur s) f x Hf Hx) as [-> | [Hin (j & Hj & Hji)]].
+ change (fr_ptr (set_fr_gen f v)) with (fr_ptr f). rewrite frame_vals_set_fr_gen.
eapply (obj_at_upd ubs2segs mem m (fr_ptr f) LAY_Frame FRAME_SIZE (frame_vals f) _ [3%nat] [(20, 24)]);
[exact Hfobj | exact (proj1 LAY_Frame_ok) | reflexivity | reflexivity | | | ].
* intros k Hk Hw. apply K; [clear - Hk Hp0 Hp1 HFRv Hac; lia | clear - Hk Hp1 Hceil HFSv HFRv Hac; lia |].
cbn [in_wins existsb fst snd] in Hw. clear - Hk Hw. intros Hc.
assert (Hb1 : (20 <=? k) && (k <? 24) = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite Hb1 in Hw. discriminate Hw.
* intros j0 fd v' Hj0 Hfd Hv'. destruct Hj0 as [<- | []]. cbn in Hfd, Hv'. injection Hfd as <-. injection Hv' as <-. exact Hfld.
* intros j0 Hj0. destruct (Nat.eq_dec j0 3) as [-> | Hne]; [exfalso; apply Hj0; left; reflexivity|].
do 9 (destruct j0 as [|j0]; [first [reflexivity | exfalso; lia] |]). reflexivity.
+ destruct (Hfgeom x Hin) as (X0 & X1 & _). pose proof (af_frames_sep API L A mem md g s N _ j i x f HH HB Hj Hf Hji) as Xf.
eapply obj_at_transport_range; [exact (Hfrs x Hin) | exact (proj1 LAY_Frame_ok) |].
intros k Hk. apply (KB (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia | clear - Xf; lia].
apply (frame_blocks_in_cgif g s N x _ _ Hin). left. reflexivity. }
assert (GO : forall ss ms' (e : sv) (pz : bool), st_ok ubs2segs E ss ms' -> ss_pc ss = FL_F2 -> ss_resv ss = None ->
(exists rg0 rg2, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ nth_error (ss_mem ss) 2 = Some rg2 /\ r_base rg2 = Some 11%nat /\
incl_chunks (fl_entry_chunks ++ [mkChunk (-160) (CVal 8 (SOff 10 0)); mkChunk (-152) (CVal 8 (SOff 11 0))]) (r_chunks rg0) = true /\
In (mkChunk 20 (CVal 4 e)) (r_chunks rg2)) ->
(if pz then frame_ptr (nth (i - 1) (cg_frames s) None) = 0 else frame_ptr (nth (i - 1) (cg_frames s) None) <> 0) ->
(pz = true -> Z.land (U E e) 3 = 0) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [3; 4]%bv = true ->
sr_get (ss_regs ss) 2%bv = SOff 2 (-272) -> sr_get (ss_regs ss) 16%bv = SOff 11 0 ->
sr_get (ss_regs ss) 18%bv = (if pz then SLit 0 else SOff 12 0) ->
sr_get (ss_regs ss) 12%bv = SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 1) ->
sr_get (ss_regs ss) 27%bv = SOff 52 0 -> sr_get (ss_regs ss) 19%bv = SOff 53 0 ->
sr_get (ss_regs ss) 10%bv = SExt true 32 (SOff 64 0) ->
journal ubs2_msyms MR FLUSH_STK sp0 FP L A mem md L A (ms_mem ms') md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs mem a) ->
SR ubs2segs (mkCfg ms' md) (fl_post API regs g s N i rest FP L A mem md)).
{ intros ss ms' e pz HS' Hpc Hrv (rg0 & rg2 & Hrg0 & Hb0 & Hrg2 & Hb2 & Hincl & Hin20) Hpz He3 Hkl Q2 Q16 Q18 Q12 Q27 Q19 Q10 HJ' K.
pose proof (regs_kept_of_st_ok ubs2segs _ ss ms' regs _ _ HS' (env_agree_refl _ _) Hkl) as R.
pose proof (st_region_chunks ubs2segs E ss ms' 0 rg0 2%nat sp0 HS' Hrg0 Hb0 HU2) as Hcs0.
apply incl_chunks_sound in Hincl.
assert (CW : forall off e0 v, In (mkChunk off (CVal 8 e0)) [mkChunk (-160) (CVal 8 (SOff 10 0)); mkChunk (-152) (CVal 8 (SOff 11 0))] ->
sv_denot E e0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> word_mem ubs2segs (ms_mem ms') (sp0 + off) v).
{ intros off e0 v Hin Hd Hv. apply (chunk_word E _ _ off e0 v); [| exact Hd | exact Hv].
apply (proj1 (Forall_forall _ _) Hcs0). apply Hincl. apply in_app_iff. right. exact Hin. }
assert (RGx : forall (r : reg) sv, sr_get (ss_regs ss) r = sv -> getr (ms_regs ms') r = sv_denot E sv).
{ intros r sv Hr. rewrite (st_ok_reg ubs2segs E ss ms' r HS'), Hr. reflexivity. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
eapply (fl_f2 API IMG RAWADD DIFF L A mem md regs (ms_regs ms') L A (ms_mem ms') md g N s i f (U E e mod 2 ^ 32) rest FP);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | | apply Z.mod_pos_bound; clear; lia | exact HFP | exact HB | | | | | | | | | |
| rewrite (RGx _ _ Q10); exact V10 ].
- apply (CGAT (ms_mem ms') (U E e mod 2 ^ 32) K).
eapply (st_field_low ubs2segs E ss ms' 2 rg2 11 (fr_ptr f) 20 4 e (2 ^ 32) HS' Hrg2 Hb2 Hin20 HU11 ltac:(cbn; lia) eq_refl).
- intros Hn. rewrite land3_mod32 by (apply U_range). apply He3. destruct pz; [reflexivity | exfalso; apply Hpz; rewrite Hn; reflexivity].
- eapply (fl_saved_of_entry E regs (ms_mem ms') sp0 (r_chunks rg0) Hcs0 HE). intros c Hc. apply Hincl. apply in_app_iff. left. exact Hc.
- rewrite (RGx _ _ Q2). cbn [sv_denot]. rewrite HU2. reflexivity.
- fold sp0. replace (sp0 - 272 + 112) with (sp0 + -160) by lia.
apply (CW (-160) (SOff 10 0)); [left; reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity | clear - Hg0 Hg1 Hac HGSv; lia].
- fold sp0. replace (sp0 - 272 + 120) with (sp0 + -152) by lia.
apply (CW (-152) (SOff 11 0)); [right; left; reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, HU11; reflexivity | clear - Hp0 Hp1 Hac HFRv; lia].
- rewrite (RGx _ _ Q16). cbn [sv_denot]. rewrite Z.add_0_r, HU11. reflexivity.
- rewrite (RGx _ _ Q18). destruct pz; [rewrite Hpz; reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 12%nat 12%bv eq_refl); exact G12].
- rewrite (RGx _ _ Q12). apply denot_of_U'. rewrite U_and_slit. change (zcanon 1) with 1.
replace (Z.land (U E (SExt true 32 (SOff 64 0))) 1) with (Z.land (Z.land (U E (SExt true 32 (SOff 64 0))) 3) 1) by (rewrite <- Z.land_assoc; reflexivity).
rewrite land3_sext32, (U_atom _ 64 (fr_attr f) HE64) by (clear - Rfattr; lia). rewrite <- Z.land_assoc. reflexivity.
- rewrite (RGx _ _ Q27). cbn [sv_denot]. rewrite Z.add_0_r, (HX 52%nat 7%nat _ eq_refl eq_refl), unsigned_lit_small by (clear - RW; lia). reflexivity.
- rewrite (RGx _ _ Q19). cbn [sv_denot]. rewrite Z.add_0_r, (HX 53%nat 8%nat _ eq_refl eq_refl), unsigned_lit_small by (clear - RH; lia). reflexivity.
- split; [rewrite (R 3%bv ltac:(cbv; auto 50)); reflexivity | rewrite (R 4%bv ltac:(cbv; auto 50)); reflexivity]. }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs2segs mem a = mbyte ubs2segs mem a) by (intros; reflexivity).
Ltac kstep3 KSTEP HU2 HU11 :=
let HF := get_HF in cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs2segs ?m a = mbyte ubs2segs ?m0 a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (_ <= a < _) -> ~ (_ <= a < _) -> mbyte ubs2segs m2 a = mbyte ubs2segs m0 a)
by (intros a Ha Hn1 Hn2; try rewrite <- (K a Ha Hn1 Hn2); exact (KSTEP E1 _ _ m m2 HU2 HU11 HF a Ha Hn1 Hn2));
clear HF K
end
end.
destruct (Z.eq_dec (frame_ptr (nth (i - 1) (cg_frames s) None)) 0) as [Hpz | Hpz];
[pose proof (MK true Hpz) as HS | pose proof (MK false Hpz) as HS]; clear MK.
- br_tree ltac:(idtac; let HS := get_HS in let HJ := get_HJ in jrun_to LAWS ubs2tbl_ok HS HJ FL_F2; [apply WR; [exact HU2 | exact HU11] |]; kstep3 KSTEP HU2 HU11)
ltac:(idtac; let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs2segs _ a = mbyte ubs2segs _ a |- _ =>
eapply (GO _ _ _ true HS);
[ reflexivity | reflexivity
| do 2 eexists; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [vm_compute; reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right])]
| exact Hpz
| first [ intros _; apply land3_and_m4 | intros _; apply land3_and_keep; apply land3_and_m4 | intros Hx; discriminate Hx ]
| vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| exact HJ | exact K ] end)
4%nat.
- br_tree ltac:(idtac; let HS := get_HS in let HJ := get_HJ in jrun_to LAWS ubs2tbl_ok HS HJ FL_F2; [apply WR; [exact HU2 | exact HU11] |]; kstep3 KSTEP HU2 HU11)
ltac:(idtac; let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs2segs _ a = mbyte ubs2segs _ a |- _ =>
eapply (GO _ _ _ false HS);
[ reflexivity | reflexivity
| do 2 eexists; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [vm_compute; reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right])]
| exact Hpz
| first [ intros _; apply land3_and_m4 | intros _; apply land3_and_keep; apply land3_and_m4 | intros Hx; discriminate Hx ]
| vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| exact HJ | exact K ] end)
4%nat.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
