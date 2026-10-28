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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l YI00 YI02 YI01 YI03
UI1e UI1c UI39 UI1i UI20 UI2r UI59 UI56 YI0x UI57
UI1h UI16 UI1z.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FL_MID    : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x104).
Definition FL_DIFF   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x120).
Definition FL_DIMS   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x764).
Definition FL_T      : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x844).
Definition FL_RAW    : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x9fc).
Definition FL_RAW2   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0xa24).
Definition FL_EALLOC : Z := Eval vm_compute in (ubs2_A_flushFrame + 0xa14).
Definition FL_CALLRET: Z := Eval vm_compute in (ubs2_A_flushFrame + 0xacc).
Definition FL_RET    : Z := Eval vm_compute in (ubs2_A_flushFrame + 0xad8).
Definition FL_FRAME : Z := 272.
Lemma frame_vals_set_fr_gen : forall f v, frame_vals (set_fr_gen f v) = list_set (frame_vals f) 3 v.
Proof. intros. reflexivity. Qed.
Lemma fr_ptr_set_fr_gen : forall f v, fr_ptr (set_fr_gen f v) = fr_ptr f. Proof. reflexivity. Qed.






Lemma cg_raw_flush_upd : forall s i gen rcur, cg_raw (flush_upd s i gen rcur) = cg_raw s. Proof. reflexivity. Qed.






Lemma cg_frames_flush_upd : forall s i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) ->
cg_frames (flush_upd s i gen rcur) = list_set (cg_frames s) i (Some (set_fr_gen f gen)).
Proof.
intros s i gen rcur f H. rewrite flush_upd_wf_frames. rewrite (nth_error_nth _ _ None H). reflexivity.
Qed.
Lemma In_frames_flush_upd : forall s i gen rcur f x,
nth_error (cg_frames s) i = Some (Some f) ->
In (Some x) (cg_frames (flush_upd s i gen rcur)) -> x = set_fr_gen f gen \/ (In (Some x) (cg_frames s) /\ exists j, nth_error (cg_frames s) j = Some (Some x) /\ j <> i).
Proof.
intros s i gen rcur f x Hf Hin. rewrite (cg_frames_flush_upd s i gen rcur f Hf) in Hin.
apply In_list_set in Hin as [H | (j & Hj & Hne)]; [left; congruence | right]. split; [eapply nth_error_In; exact Hj | exists j; auto].
Qed.
Lemma cgif_wf_flush_upd : forall s N i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) -> cgif_wf s N -> cgif_wf (flush_upd s i gen rcur) N.
Proof.
intros s N i gen rcur f Hf (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf).
unfold cgif_wf. rewrite (cg_frames_flush_upd s i gen rcur f Hf). cbn -[list_set Z.mul Z.land].
rewrite length_list_set. repeat (split; [assumption|]). split.
- destruct Hih as [H1 | [H2 Hn1]]; [left; exact H1 | right]. split; [exact H2|].
destruct (Nat.eq_dec i 1) as [->|Hne].
+ rewrite nth_list_set_same by (rewrite Hlen; lia). discriminate.
+ rewrite nth_list_set_other by exact Hne. exact Hn1.
- intros x Hx. apply In_list_set in Hx as [Hx1 | (j & Hj & _)].
+ injection Hx1 as ->. apply (frame_wf_fields (cg_attr s) f); [apply Hfwf; eapply nth_error_In; exact Hf | reflexivity | reflexivity].
+ apply Hfwf. eapply nth_error_In. exact Hj.
Qed.
Lemma cgif_blocks_flush_upd : forall g s N i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) -> cgif_blocks g (flush_upd s i gen rcur) N = cgif_blocks g s N.
Proof.
intros g s N i gen rcur f Hf. apply flush_upd_blocks. apply (proj1 (nth_error_Some _ _)). rewrite Hf. discriminate.
Qed.


Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Definition fl_post (regs0 : bvmap 5 word) (g : Z) (s : cgif_st) (N : Z) (i : nat) (rest FP : list (Z * Z)) L A mem md (c' : config) : Prop :=
exists L' A' regs' mem' md' (r gen' rwcur' : Z),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR FLUSH_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem' g (flush_upd s i gen' rwcur') /\ cgif_wf (flush_upd s i gen' rwcur') N /\
Permutation (blocks L' A') (cgif_blocks g s N ++ rest).
End d.
Definition FL_SAVED : list reg := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition fl_saved_vals (regs0 : bvmap 5 word) : list Z := map (fun r : reg => bv_unsigned (getr regs0 r)) FL_SAVED.
Definition fl_saved_ok (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j (r : reg), nth_error FL_SAVED j = Some r -> word_mem ubs2segs mem (sp0 - 8 - 8 * Z.of_nat j) (bv_unsigned (getr regs0 r)).
Definition fl_stk_saved (k : nat) : list YQ0b.chunk :=
map (fun j => mkChunk (264 - 8 * Z.of_nat j) (CVal 8 (SOff (k + j) 0))) (seq 0 13).
Definition fl_untouched (regs0 regs1 : bvmap 5 word) : Prop :=
getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4.
Lemma fl_saved_vals_nth : forall regs0 j r,
nth_error FL_SAVED j = Some r -> nth_error (fl_saved_vals regs0) j = Some (bv_unsigned (getr regs0 r)).
Proof. intros regs0 j r H. unfold fl_saved_vals. rewrite nth_error_map, H. reflexivity. Qed.
Lemma fl_saved_ok_kept : forall m m' sp0 regs0,
fl_saved_ok m sp0 regs0 -> (forall a, sp0 - 104 <= a < sp0 -> mbyte ubs2segs m' a = mbyte ubs2segs m a) -> fl_saved_ok m' sp0 regs0.
Proof.
intros m m' sp0 regs0 H Hf j r Hr k Hk.
assert (Hj : (j < 13)%nat) by (apply (proj1 (nth_error_Some FL_SAVED j)); rewrite Hr; discriminate).
rewrite Hf by lia. apply (H j r Hr). exact Hk.
Qed.
Lemma fl_saved_chunks_ok : forall E mem sp0 regs0 k,
fl_saved_ok mem sp0 regs0 ->
(forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
Forall (chunk_ok ubs2segs E mem (sp0 - 272)) (fl_stk_saved k).
Proof.
intros E mem sp0 regs0 k HS HK.
unfold fl_stk_saved. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
destruct (nth_error FL_SAVED j) as [r|] eqn:Hr.
2:{ exfalso. apply nth_error_None in Hr. cbn in Hr. lia. }
eapply (chunk_ok_val _ _ _ _ _ _ _ (bv_unsigned (getr regs0 r))).
- cbn [sv_denot]. rewrite Z.add_0_r, (HK j _ (fl_saved_vals_nth regs0 j r Hr)), Z_to_bv_bv_unsigned. reflexivity.
- cbn. apply u64_range_getr.
- cbn. lia.
- apply val_mem_word_mem. replace (sp0 - 272 + (264 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact (HS j r Hr).
Qed.

Definition A_K : nat := 32.
Definition A_X : nat := 45.
Definition A_F : nat := 62.
Definition A_B : nat := 71.
Definition A_Mo : nat := 80.
Definition fb_vals (fb : option frame_st) : list Z :=
match fb with Some b => frame_vals b | None => [0; 0; 0; 0; 0; 0; 0; 0; 0] end.
Lemma fb_vals_length : forall fb, length (fb_vals fb) = 9%nat.
Proof. intros [b|]; reflexivity. Qed.
Definition fl_AL (regs0 : bvmap 5 word) (s : cgif_st) (f : frame_st) (fb : option frame_st) (more : list Z) : list Z :=
fl_saved_vals regs0 ++ cgif_vals s ++ frame_vals f ++ fb_vals fb ++ more.
Definition fl_E (regs1 regs0 : bvmap 5 word) (s : cgif_st) (f : frame_st) (fb : option frame_st) (more : list Z) : env :=
Ereg regs1 (map (Z_to_bv 64) (fl_AL regs0 s f fb more) ++ []).
Definition fl_litsG : list (option Z) := litsG None None None None.
Definition fl_Rg : YQ0b.region := YQ0b.mkRegion (Some 8%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG).
Definition fl_Rg_part (lo hi : Z) : YQ0b.region :=
YQ0b.mkRegion (Some 8%nat) lo hi 0 0 (chunks_between lo hi (obj_chunks_gen LAY_CGIF A_X fl_litsG)).
Definition fl_Rf (wlo whi : Z) : YQ0b.region := YQ0b.mkRegion (Some 9%nat) 0 40 wlo whi (obj_chunks_gen LAY_Frame A_F []).
Definition fl_Rf_part (lo hi wlo whi : Z) : YQ0b.region :=
YQ0b.mkRegion (Some 9%nat) lo hi wlo whi (chunks_between lo hi (obj_chunks_gen LAY_Frame A_F [])).
Definition fl_Rfb (n : nat) : YQ0b.region := YQ0b.mkRegion (Some n) 0 40 0 0 (obj_chunks_gen LAY_Frame A_B []).
Definition fl_Rfb_part (n : nat) (lo hi : Z) : YQ0b.region :=
YQ0b.mkRegion (Some n) lo hi 0 0 (chunks_between lo hi (obj_chunks_gen LAY_Frame A_B [])).
Definition fl_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (8%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(9%nat, mkAF 4096 (CEIL_MAX - 40) 3) ].
Definition fl_gfacts : list (nat * afact) :=
[ (50%nat, mkAF 0 4294967295 0)  ; (51%nat, mkAF 0 4294967295 0)  ;
(52%nat, mkAF 1 65535 0)  ; (53%nat, mkAF 1 65535 0)  ; (54%nat, mkAF 0 65535 0)  ;
(58%nat, mkAF 4096 CEIL_MAX 0)   ].
Definition fl_ffacts : list (nat * afact) :=
[ (62%nat, mkAF 0 (2^64 - 1) 0); (63%nat, mkAF 4096 CEIL_MAX 0); (64%nat, mkAF 0 4294967295 0); (65%nat, mkAF 0 4294967295 0);
(66%nat, mkAF 0 65535 0); (67%nat, mkAF 0 65535 0); (68%nat, mkAF 0 255 0); (69%nat, mkAF 0 255 0); (70%nat, mkAF 0 255 0) ].
Definition fl_bfacts : list (nat * afact) :=
[ (71%nat, mkAF 0 (2^64 - 1) 0); (72%nat, mkAF 4096 CEIL_MAX 0); (73%nat, mkAF 0 4294967295 0); (74%nat, mkAF 0 4294967295 0);
(75%nat, mkAF 0 65535 0); (76%nat, mkAF 0 65535 0); (77%nat, mkAF 0 255 0); (78%nat, mkAF 0 255 0); (79%nat, mkAF 0 255 0) ].
Section e.
Variables (regs1 regs0 : bvmap 5 word) (s : cgif_st) (f : frame_st) (fb : option frame_st) (more : list Z).
Let E := fl_E regs1 regs0 s f fb more.
Lemma fl_HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr.
Proof. intros n rr H. unfold E, fl_E. apply ew_Ereg_nat. exact H. Qed.
Lemma fl_HA : forall j v, nth_error (fl_AL regs0 s f fb more) j = Some v -> ew E (32 + j) = Z_to_bv 64 v.
Proof. intros j v H. unfold E, fl_E. apply Ereg_vals. exact H. Qed.
Lemma fl_HK : forall n j v, n = (32 + j)%nat -> nth_error (fl_saved_vals regs0) j = Some v -> ew E n = Z_to_bv 64 v.
Proof.
intros n j v -> H. apply fl_HA. unfold fl_AL. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma fl_HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error FL_SAVED j = Some r -> ew E n = getr regs0 r.
Proof. intros n j r Hn Hr. rewrite (fl_HK n j _ Hn (fl_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. Qed.
Lemma fl_HX : forall n j v, n = (45 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v.
Proof.
intros n j v -> H. replace (45 + j)%nat with (32 + (length (fl_saved_vals regs0) + j))%nat by reflexivity.
apply fl_HA. unfold fl_AL. rewrite nth_error_app_len. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma fl_HF : forall n j v, n = (62 + j)%nat -> nth_error (frame_vals f) j = Some v -> ew E n = Z_to_bv 64 v.
Proof.
intros n j v -> H. replace (62 + j)%nat with (32 + (length (fl_saved_vals regs0 ++ cgif_vals s) + j))%nat by reflexivity.
apply fl_HA. unfold fl_AL. rewrite app_assoc, nth_error_app_len. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma fl_HB : forall n j v, n = (71 + j)%nat -> nth_error (fb_vals fb) j = Some v -> ew E n = Z_to_bv 64 v.
Proof.
intros n j v -> H. replace (71 + j)%nat with (32 + (length (fl_saved_vals regs0 ++ cgif_vals s ++ frame_vals f) + j))%nat by (rewrite !length_app; reflexivity).
apply fl_HA. unfold fl_AL. rewrite 2!app_assoc, nth_error_app_len. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma fl_HM : forall n j v, n = (80 + j)%nat -> nth_error more j = Some v -> ew E n = Z_to_bv 64 v.
Proof.
intros n j v -> H.
replace (80 + j)%nat with (32 + (length (fl_saved_vals regs0 ++ cgif_vals s ++ frame_vals f ++ fb_vals fb) + j))%nat
by (rewrite !length_app, fb_vals_length; reflexivity).
apply fl_HA. unfold fl_AL. rewrite 3!app_assoc, nth_error_app_len. exact H.
Qed.
Lemma fl_Rg_ok : forall mem g,
bv_unsigned (ew E 8) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs2segs mem g LAY_CGIF (cgif_vals s) -> region_ok ubs2segs E mem fl_Rg.
Proof.
intros mem g H8 Hlo Hhi Hobj. unfold fl_Rg, fl_litsG, A_X.
eapply (region_ok_obj_gen ubs2segs E mem 8 g 96 0 0 LAY_CGIF (cgif_vals s) 45 (litsG None None None None));
[exact H8 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros i Hi; lia].
intros j v Hj. apply (fl_HX (45 + j) j v eq_refl Hj).
Qed.

Lemma fl_Rf_ok : forall mem p wlo whi,
bv_unsigned (ew E 9) = p -> p = fr_ptr f -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs2segs mem p LAY_Frame (frame_vals f) ->
(forall i, wlo <= i < whi -> writable_at ubs2segs mem (p + i)) ->
region_ok ubs2segs E mem (fl_Rf wlo whi).
Proof.
intros mem p wlo whi H9 Hp Hlo Hhi Hobj Hw. unfold fl_Rf, A_F.
eapply (region_ok_obj_gen ubs2segs E mem 9 p 40 wlo whi LAY_Frame (frame_vals f) 62 []);
[exact H9 | lia | lia | exact Hobj | reflexivity | | intros [|j] z Hz; discriminate Hz | exact Hw].
intros j v Hj. apply (fl_HF (62 + j) j v eq_refl Hj).
Qed.

Lemma fl_Rfb_ok : forall mem (n : nat) p b,
bv_unsigned (ew E n) = p -> fb = Some b -> p = fr_ptr b -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs2segs mem p LAY_Frame (frame_vals b) ->
region_ok ubs2segs E mem (fl_Rfb n).
Proof.
intros mem n p b Hn Hfb Hp Hlo Hhi Hobj. unfold fl_Rfb, A_B.
eapply (region_ok_obj_gen ubs2segs E mem n p 40 0 0 LAY_Frame (frame_vals b) 71 []);
[exact Hn | lia | lia | exact Hobj | reflexivity | | intros [|j] z Hz; discriminate Hz | intros i Hi; lia].
intros j v Hj. apply (fl_HB (71 + j) j v eq_refl). rewrite Hfb. exact Hj.
Qed.

Lemma fl_gfacts_ok : forall mem g N, obj_at ubs2segs mem g LAY_CGIF (cgif_vals s) -> cgif_wf s N ->
4096 <= cg_raw s -> cg_raw s <= alloc_ceiling -> atoms_ok E fl_gfacts.
Proof.
intros mem g N Hobj Hwf Hr0 Hr1. pose proof (obj_at_range _ _ _ _ _ Hobj) as R.
pose proof Hwf as (_ & HW1 & HH1 & _).
cbn [atoms_ok fl_gfacts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (2 ^ 0) with 1.
rewrite (fl_HX 50 5 (cg_attr s) eq_refl eq_refl), (fl_HX 51 6 (cg_gen s) eq_refl eq_refl), (fl_HX 52 7 (cg_W s) eq_refl eq_refl),
(fl_HX 53 8 (cg_H s) eq_refl eq_refl), (fl_HX 54 9 (cg_ngp s) eq_refl eq_refl), (fl_HX 58 13 (cg_raw s) eq_refl eq_refl).
pose proof (R 5%nat _ eq_refl) as R5. pose proof (R 6%nat _ eq_refl) as R6. pose proof (R 7%nat _ eq_refl) as R7.
pose proof (R 8%nat _ eq_refl) as R8. pose proof (R 9%nat _ eq_refl) as R9. pose proof (R 13%nat _ eq_refl) as R13.
cbn [nth snd LAY_CGIF Z.of_N] in R5, R6, R7, R8, R9, R13.
pose proof (proj1 alloc_ceiling_val).
rewrite !unsigned_lit_small by lia. rewrite !Z.mod_1_r. repeat split; lia.
Qed.
Lemma fl_ffacts_ok : forall mem p, obj_at ubs2segs mem p LAY_Frame (frame_vals f) ->
4096 <= fr_img f -> fr_img f <= alloc_ceiling -> atoms_ok E fl_ffacts.
Proof.
intros mem p Hobj Hi0 Hi1. pose proof (obj_at_range _ _ _ _ _ Hobj) as R.
cbn [atoms_ok fl_ffacts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (2 ^ 0) with 1.
rewrite (fl_HF 62 0 _ eq_refl eq_refl), (fl_HF 63 1 _ eq_refl eq_refl), (fl_HF 64 2 _ eq_refl eq_refl), (fl_HF 65 3 _ eq_refl eq_refl),
(fl_HF 66 4 _ eq_refl eq_refl), (fl_HF 67 5 _ eq_refl eq_refl), (fl_HF 68 6 _ eq_refl eq_refl), (fl_HF 69 7 _ eq_refl eq_refl),
(fl_HF 70 8 _ eq_refl eq_refl).
pose proof (R 0%nat _ eq_refl) as R0. pose proof (R 1%nat _ eq_refl) as R1. pose proof (R 2%nat _ eq_refl) as R2.
pose proof (R 3%nat _ eq_refl) as R3. pose proof (R 4%nat _ eq_refl) as R4. pose proof (R 5%nat _ eq_refl) as R5.
pose proof (R 6%nat _ eq_refl) as R6. pose proof (R 7%nat _ eq_refl) as R7. pose proof (R 8%nat _ eq_refl) as R8.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in R0, R1, R2, R3, R4, R5, R6, R7, R8.
pose proof (proj1 alloc_ceiling_val).
rewrite !unsigned_lit_small by lia. rewrite !Z.mod_1_r. repeat split; lia.
Qed.
Lemma fl_bfacts_ok : forall mem p b, fb = Some b -> obj_at ubs2segs mem p LAY_Frame (frame_vals b) ->
4096 <= fr_img b -> fr_img b <= alloc_ceiling -> atoms_ok E fl_bfacts.
Proof.
intros mem p b Hfb Hobj Hi0 Hi1. pose proof (obj_at_range _ _ _ _ _ Hobj) as R.
assert (HBb : forall n j v, n = (71 + j)%nat -> nth_error (frame_vals b) j = Some v -> ew E n = Z_to_bv 64 v).
{ intros n j v Hn Hj. apply (fl_HB n j v Hn). rewrite Hfb. exact Hj. }
cbn [atoms_ok fl_bfacts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (2 ^ 0) with 1.
rewrite (HBb 71%nat 0%nat _ eq_refl eq_refl), (HBb 72%nat 1%nat _ eq_refl eq_refl), (HBb 73%nat 2%nat _ eq_refl eq_refl), (HBb 74%nat 3%nat _ eq_refl eq_refl),
(HBb 75%nat 4%nat _ eq_refl eq_refl), (HBb 76%nat 5%nat _ eq_refl eq_refl), (HBb 77%nat 6%nat _ eq_refl eq_refl), (HBb 78%nat 7%nat _ eq_refl eq_refl),
(HBb 79%nat 8%nat _ eq_refl eq_refl).
pose proof (R 0%nat _ eq_refl) as R0. pose proof (R 1%nat _ eq_refl) as R1. pose proof (R 2%nat _ eq_refl) as R2.
pose proof (R 3%nat _ eq_refl) as R3. pose proof (R 4%nat _ eq_refl) as R4. pose proof (R 5%nat _ eq_refl) as R5.
pose proof (R 6%nat _ eq_refl) as R6. pose proof (R 7%nat _ eq_refl) as R7. pose proof (R 8%nat _ eq_refl) as R8.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in R0, R1, R2, R3, R4, R5, R6, R7, R8.
pose proof (proj1 alloc_ceiling_val).
rewrite !unsigned_lit_small by lia. rewrite !Z.mod_1_r. repeat split; lia.
Qed.
End e.
Section h.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Definition fl_inv (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z) (rest : list (Z * Z)) (tmp : list (Z * Z)) : Prop :=
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\
(i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks g s N ++ rest).
Lemma fl_img_geom : forall L A m md g s N rest f,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks g s N ++ rest) -> In (Some f) (cg_frames s) -> 1 <= N ->
4096 <= fr_img f /\ fr_img f + N <= alloc_ceiling.
Proof.
intros L A m md g s N rest f HH HB Hin HN.
destruct (af_frame_geom API L A m md g s N rest f HH HB Hin) as (_ & Himg & _).
exact (blocks_range _ _ LAWS L A m md (fr_img f) N HH Himg).
Qed.
End h.
Lemma perm_img_front : forall {X} (g r x i : X) (pal F1 pf F2 rest : list X),
Permutation (g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest) (r :: g :: i :: (pal ++ F1 ++ x :: pf ++ F2) ++ rest).
Proof.
intros.
assert (E1 : g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest = (g :: r :: pal ++ F1 ++ [x]) ++ i :: ((pf ++ F2) ++ rest)).
{ cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
assert (E2 : r :: g :: i :: (pal ++ F1 ++ x :: pf ++ F2) ++ rest = r :: g :: i :: (pal ++ F1 ++ [x]) ++ ((pf ++ F2) ++ rest)).
{ cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
rewrite E1, E2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
change (i :: (g :: r :: pal ++ F1 ++ [x]) ++ (pf ++ F2) ++ rest) with ((i :: g :: r :: pal ++ F1 ++ [x]) ++ (pf ++ F2) ++ rest).
change (r :: g :: i :: (pal ++ F1 ++ [x]) ++ (pf ++ F2) ++ rest) with ((r :: g :: i :: pal ++ F1 ++ [x]) ++ (pf ++ F2) ++ rest).
apply Permutation_app_tail.
eapply Permutation_trans; [apply perm_swap|]. eapply Permutation_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap.
Qed.
Lemma flush_blocks_img0 : forall g s N rest i f, nth_error (cg_frames s) i = Some (Some f) ->
exists rest0, Permutation (cgif_blocks g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (fr_img f, N) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0).
Proof.
intros g s N rest i f Hf.
destruct (nth_error_split _ _ Hf) as (l1 & l2 & Hfr & Hl1).
exists ((pal_blocks s ++ frames_blocks N l1 ++ (fr_ptr f, FRAME_SIZE) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) ++ frames_blocks N l2) ++ rest).
split.
- unfold cgif_blocks. rewrite Hfr, frames_blocks_app, frames_blocks_cons_some. unfold frame_blocks at 1.
cbn [app]. apply perm_img_front.
- intros Ha. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. right.
apply in_app_iff. left. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
Lemma flush_blocks_img1 : forall g s N rest f p Nt, In (Some f) (cg_frames s) ->
exists rest0, Permutation ((p, Nt) :: cgif_blocks g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (p, Nt) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0).
Proof.
intros g s N rest f p Nt Hf.
exists ((pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest). split.
- unfold cgif_blocks. cbn [app].
eapply Permutation_trans; [apply perm_skip; apply perm_swap|].
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
- intros Ha. apply in_app_iff. left. apply in_app_iff. right.
unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hf|].
unfold frame_blocks. right. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
