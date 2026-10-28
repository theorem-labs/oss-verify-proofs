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
UI1h UI1g.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma cgif_vals_flush_upd : forall s i gen' rwcur', cgif_vals (flush_upd s i gen' rwcur') = cgif_vals s.
Proof. intros. unfold cgif_vals. rewrite !flush_upd_frames_shape. reflexivity. Qed.
Lemma lxor_ones_low : forall u, 0 <= u < 2 ^ 64 -> (Z.lxor u (Z.ones 64)) mod 2 ^ 64 = 2 ^ 64 - 1 - u.
Proof.
intros u Hu. transitivity (Z.lnot u mod 2 ^ 64).
- apply Z.bits_inj'. intros i Hi. destruct (Z.ltb_spec i 64) as [Hl|Hl].
+ rewrite !Z.mod_pow2_bits_low by exact Hl. rewrite Z.lxor_spec, Z.lnot_spec, Z.ones_spec_low by lia. destruct (Z.testbit u i); reflexivity.
+ rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
- unfold Z.lnot. replace (Z.pred (- u)) with ((2 ^ 64 - 1 - u) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_not_atom : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit.
change (zcanon (-1)) with (Z.ones 64). unfold zcanon, M64. apply lxor_ones_low. exact Hx.
Qed.
Lemma denot_not_atom : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof. intros E n x Hn Hx. rewrite denot_lit_U. f_equal. exact (U_not_atom E n x Hn Hx). Qed.
End d.
Ltac add_region HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Ltac hist slv :=
repeat match goal with
| |- mbyte _ ?m ?a = mbyte _ ?m ?a => reflexivity
| HF : frame_of _ _ ?m0 ?m |- mbyte _ ?m ?a = _ => mb_frame_with HF ltac:(lia) slv
end.
Ltac wr_any HU2 HU8 Hgin HFPin :=
repeat first [ apply wr_ok_nil
| apply wr_ok_cons_ro; [cbn; lia|]
| eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]
| eapply wr_ok_cons_block with (m := CGIF_SIZE);
[ reflexivity | ew_havocA; exact HU8 | exact Hgin | cbn; lia | unfold CGIF_SIZE; cbn; lia
| cbv [cl_R2 r_wlo r_whi]; intros a Ha; eapply (HFPin _ CGIF_SIZE a); [left; reflexivity | unfold CGIF_SIZE; lia] | ] ].
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_iter2 : sstate :=
mkSS CL_LOOP (sr_set (sr_set (sr_set sr_atoms 18%bv (SOff 8 16)) 19%bv (SLit 16)) 20%bv (SLit 24))
[ YQ0b.mkRegion (Some 2%nat) 0 48 0 48 cl_saved ; cl_R1 ; cl_R2 ]
None (mkFacts cl_facts [] []).
End e.
Ltac reg_not HS HE G10 :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in
pose proof (st_ok_reg ubs2segs Ec ssc msc 9%bv HS) as T; eval_sr_get_in T;
cbn [ms_regs mkst]; rewrite T; clear T;
apply denot_not_atom; [ew_havocA; rewrite (HE 10%nat 10%bv eq_refl); exact G10 | lia]
end.
Ltac cgif_obj_now_p p i1 i2 HS HU8 HXn Rg s cur ecur tcur :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch type of HU8 with bv_unsigned _ = ?g =>
assert (obj_at ubs2segs (ms_mem msc) g LAY_CGIF (vals15 s ++ [cur; cg_ihead s]));
[ apply obj_cgif_join;
[ eapply (st_obj_at ubs2segs _ _ _ i1 _ p g LAY15 (vals15 s) 32 lits15 HS eq_refl eq_refl ltac:(ew_havocA; exact HU8));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; split;
[ let Hlj := fresh "Hlj" in assert (Hlj : (j < length (vals15 s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate); change (length (vals15 s)) with 15%nat in Hlj;
replace (nth j LAY15 (0, 8%N)) with (nth j LAY_CGIF (0, 8%N)) by (do 15 (destruct j as [|j]; [reflexivity|]); exfalso; lia);
apply (Rg j v); rewrite cgif_vals_split, nth_error_app1 by exact Hlj; exact Hj
| do 15 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits15];
first [reflexivity | ew_havocA; apply (HXn _ _ _ eq_refl); reflexivity] |]);
exfalso; destruct j; cbn in Hj; discriminate Hj ]
| replace (g + 88) with (bv_unsigned (ew Ec p) + 88) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_val ubs2segs _ _ _ i2 _ p 88 4%N ecur _ cur HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | tcur | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption
| replace (g + 92) with (bv_unsigned (ew Ec p) + 92) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_val ubs2segs _ _ _ i2 _ p 92 4%N (SOff 48 0) _ (cg_ihead s) HS);
[reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption ]
| ] end end.
Ltac cgif_obj_low_p p i1 i2 HS HU8 HXn Rg s k :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch type of HU8 with bv_unsigned _ = ?g =>
assert (obj_at ubs2segs (ms_mem msc) g LAY_CGIF (vals15 s ++ [U Ec (SOff k 0) mod 2 ^ 32; cg_ihead s]));
[ apply obj_cgif_join;
[ eapply (st_obj_at ubs2segs _ _ _ i1 _ p g LAY15 (vals15 s) 32 lits15 HS eq_refl eq_refl ltac:(ew_havocA; exact HU8));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; split;
[ let Hlj := fresh "Hlj" in assert (Hlj : (j < length (vals15 s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate); change (length (vals15 s)) with 15%nat in Hlj;
replace (nth j LAY15 (0, 8%N)) with (nth j LAY_CGIF (0, 8%N)) by (do 15 (destruct j as [|j]; [reflexivity|]); exfalso; lia);
apply (Rg j v); rewrite cgif_vals_split, nth_error_app1 by exact Hlj; exact Hj
| do 15 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits15];
first [reflexivity | ew_havocA; apply (HXn _ _ _ eq_refl); reflexivity] |]);
exfalso; destruct j; cbn in Hj; discriminate Hj ]
| replace (g + 88) with (bv_unsigned (ew Ec p) + 88) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_lowv _ _ _ i2 _ p 88 4%N (SOff k 0) _ 4%nat (2 ^ 32) HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity | reflexivity]
| pose proof (Z.mod_pos_bound (U Ec (SOff k 0)) (2 ^ 32) ltac:(lia)); lia
| replace (g + 92) with (bv_unsigned (ew Ec p) + 92) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_val ubs2segs _ _ _ i2 _ p 92 4%N (SOff 48 0) _ (cg_ihead s) HS);
[reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption ]
| ] end end.
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis FLUSH : flush_spec API.
Lemma cgif_geom : forall L A m md g s N rest,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
(4096 <= cg_raw s /\ cg_raw s + RAW_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= cg_raw s \/ cg_raw s + RAW_SIZE <= g)) /\
(forall f, In (Some f) (cg_frames s) -> 4096 <= fr_ptr f /\ fr_ptr f + FRAME_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= g)) /\
(4096 <= g /\ g + CGIF_SIZE <= alloc_ceiling /\ g mod 16 = 0).
Proof.
intros L A m md g s N rest HH HB.
assert (Hsub : forall x, In x (cgif_blocks g s N) -> In x (blocks L A)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hx. }
assert (Hsep : forall y, In y ((cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s)) -> g + CGIF_SIZE <= fst y \/ fst y + snd y <= g).
{ intros y Hy. apply (heap_sep_perm _ _ LAWS L A m md (g, CGIF_SIZE) (((cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest) y HH).
- exact HB.
- apply in_app_iff. left. exact Hy. }
split; [|split].
- destruct (blocks_range _ _ LAWS L A m md (cg_raw s) RAW_SIZE HH (Hsub _ ltac:(right; left; reflexivity))) as [R0 R1].
pose proof (Hsep (cg_raw s, RAW_SIZE) ltac:(left; reflexivity)) as Hs. cbn [fst snd] in Hs. unfold RAW_SIZE, CGIF_SIZE in *. lia.
- intros f Hin. pose proof (frames_blocks_ptr_in N (cg_frames s) f Hin) as Hm.
destruct (blocks_range _ _ LAWS L A m md (fr_ptr f) FRAME_SIZE HH (Hsub _ ltac:(right; right; apply in_app_iff; right; exact Hm))) as [R0 R1].
pose proof (Hsep (fr_ptr f, FRAME_SIZE) ltac:(right; apply in_app_iff; right; exact Hm)) as Hs. cbn [fst snd] in Hs. lia.
- exact (heap_blocks_range _ _ LAWS L A m md g CGIF_SIZE HH (Hsub _ ltac:(left; reflexivity)) ltac:(unfold CGIF_SIZE; lia)).
Qed.
Lemma close_iter2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z)),
let sp0 := spZ regs0 in
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> sp0 mod 16 = 0 ->
(forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
cgif_at memc g s -> cgif_wf s N ->
Permutation (blocks Lc Ac) (cgif_blocks g s N ++ rest) ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 48) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (2 ^ 64 - 1 - g) ->
getr regs1 18 = Z_to_bv 64 (g + 16) -> getr regs1 19 = Z_to_bv 64 16 -> getr regs1 20 = Z_to_bv 64 24 ->
cl_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_LOOP) memc (seg_rom ubs2segs)) mdc) (close_post API regs0 FP L A mem md rest).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP sp0 HJ Hid Hra0 Htp0 Hal16 HFPin HFPlow Hat Hwf HB HSV G2 G8 G9 G18 G19 G20 HUT.
pose proof HUT as (G3 & G4 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof Hwf as (Hlen & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 48) mod 16 = 0) by (replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (cgif_geom Lc Ac memc mdc g s N rest HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error (cgif_vals s) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HXn : forall n j v, n = (32 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) by (intros n j v -> Hj; apply HX; exact Hj).
assert (HY : forall j v, nth_error (cl_saved_vals regs0) j = Some v -> ew E (49 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (49 + j)%nat with (32 + (length (cgif_vals s) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HW49 : ew E 49 = getr regs0 1) by (etransitivity; [apply (HY 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW50 : ew E 50 = getr regs0 8) by (etransitivity; [apply (HY 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW51 : ew E 51 = getr regs0 9) by (etransitivity; [apply (HY 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW52 : ew E 52 = getr regs0 18) by (etransitivity; [apply (HY 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW53 : ew E 53 = getr regs0 19) by (etransitivity; [apply (HY 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW54 : ew E 54 = getr regs0 20) by (etransitivity; [apply (HY 5%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = 2 ^ 64 - 1 - g) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok ubs2segs E ss_iter2 (mkst regs1 (Z_to_bv 64 CL_LOOP) memc (seg_rom ubs2segs))).
{ unfold ss_iter2. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |] | intros H0; discriminate H0 |] | intros H0; discriminate H0 |];
cbn [sv_denot]; [rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl), G8, unsigned_lit_small by lia; exact G18 | exact G19 | exact G20].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 48 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 48) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HY j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold cl_saved.
apply Forall_cons; [apply (CK 40 0%nat _ eq_refl); [replace (sp0 - 48 + 40) with (sp0 - 8) by lia; exact W1 | apply u64_range']|].
apply Forall_cons; [apply (CK 32 1%nat _ eq_refl); [replace (sp0 - 48 + 32) with (sp0 - 16) by lia; exact W8 | apply u64_range']|].
apply Forall_cons; [apply (CK 24 2%nat _ eq_refl); [replace (sp0 - 48 + 24) with (sp0 - 24) by lia; exact W9 | apply u64_range']|].
apply Forall_cons; [apply (CK 16 3%nat _ eq_refl); [replace (sp0 - 48 + 16) with (sp0 - 32) by lia; exact W18 | apply u64_range']|].
apply Forall_cons; [apply (CK 8 4%nat _ eq_refl); [replace (sp0 - 48 + 8) with (sp0 - 40) by lia; exact W19 | apply u64_range']|].
apply Forall_cons; [apply (CK 0 5%nat _ eq_refl); [replace (sp0 - 48 + 0) with (sp0 - 48) by lia; exact W20 | apply u64_range']|].
apply Forall_nil.
+ unfold cl_R1. eapply (region_ok_obj_gen ubs2segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, HU9, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_LOOP) memc (seg_rom ubs2segs))) in HJ.
jrun LAWS ubs2tbl_ok HS HJ. { wr_any HU2 HU8 Hgin HFPin. }
assert (TR : forall m', (forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs2segs m' a = mbyte ubs2segs memc a) ->
obj_at ubs2segs m' (cg_raw s) LAY_Raw (raw_vals g s) /\ (forall f, In (Some f) (cg_frames s) -> obj_at ubs2segs m' (fr_ptr f) LAY_Frame (frame_vals f))).
{ intros m' Hm'. split.
- eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply Hm'; lia.
- intros f Hin. destruct (Hfgeom f Hin) as (F0 & F1 & F2). eapply obj_at_transport_range; [exact (Hfrs f Hin) | exact (proj1 LAY_Frame_ok)|]. intros i Hi. apply Hm'; lia. }
jbranch ubs2tbl HS.
-
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ CL_CLEAN. { wr_any HU2 HU8 Hgin HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia))) as [Hraw2 Hfrs2] end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_clean API IMG L A mem md regs0 rg Lc Ac mm mdc g N s rest FP) end;
[ exact HJ | exact Hra0 | exact Htp0 | exact Hal16 | exact HFPin | exact HFPlow | | exact Hwf | exact HB | | | | | ].
+ split; [exact Hobj2 | split; [exact Hraw2 | exact Hfrs2]].
+ unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 48 + (48 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 40 (SOff 49 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 32 (SOff 50 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 51 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 52 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 53 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW53, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 0 (SOff 54 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW54, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; reflexivity).
+ reg_nowF HS ltac:(rewrite HU8; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ unfold cl_untouched; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
-
rewrite branch_eq_U, (U_atom _ 34 (frame_ptr (nth 2 (cg_frames s) None))), U_lit in Hc;
[| lia | ew_havocA; apply (HXn 34%nat 2%nat _ eq_refl eq_refl) | ].
2:{ pose proof (Rg 2%nat _ eq_refl) as R34. cbn [nth snd LAY_CGIF Z.of_N] in R34. lia. }
destruct (nth 2 (cg_frames s) None) as [f2|] eqn:Hn2; [| cbn in Hc; discriminate Hc]. clear Hc.
assert (Ho2 : nth_error (cg_frames s) 2 = Some (Some f2)) by (rewrite (nth_error_nth' _ None) by lia; rewrite Hn2; reflexivity).
assert (Hf2in : In (Some f2) (cg_frames s)) by (eapply nth_error_In; exact Ho2).
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_flushFrame. { wr_any HU2 HU8 Hgin HFPin. }
jreg HS (10%bv:reg) as Hm10. jreg HS (11%bv:reg) as Hm11. jreg HS (12%bv:reg) as Hm12.
jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4. jreg HS (1%bv:reg) as Hm1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 48) by (unfold spZ; rewrite Hm2; apply unsigned_lit_small; lia) end.
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj1 end. rewrite <- cgif_vals_split in Hobj1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia))) as [Hraw1 Hfrs1] end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2 (r gen' rwcur' : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs2_A_cgif_close + 0x5c)) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 2 gen' rwcur') /\ cgif_wf (flush_upd s 2 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks g s N ++ rest) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 48 - FLUSH_STK <= x < sp0 - 48) ->
mbyte ubs2segs mem2 x = mbyte ubs2segs (ms_mem msx) x /\ (writable_at ubs2segs (ms_mem msx) x <-> writable_at ubs2segs mem2 x)))
end.
{ eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FLUSH_STK) (FP1 := blocks_fp (cgif_blocks g s N))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => exists r gen' rwcur' : Z,
st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 2 gen' rwcur') /\ cgif_wf (flush_upd s 2 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks g s N ++ rest));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FLUSH_STK; lia | rewrite Hsp; unfold FLUSH_STK; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (FLUSH Lc Ac _ _ mdc g s N 2%nat f2 rest HPRE1 Hid); [ | | exact Hwf | right; reflexivity | exact Ho2 | | | exact HB ].
+ rewrite Hm10. ew_havocA. rewrite <- HU8. symmetry. apply Z_to_bv_bv_unsigned.
+ split; [exact Hobj1 | split; [exact Hraw1 | exact Hfrs1]].
+ rewrite Hm11. ew_havocA. rewrite (HXn 34%nat 2%nat _ eq_refl eq_refl), Hn2. reflexivity.
+ rewrite Hm12. ew_havocA. rewrite (HXn 33%nat 1%nat _ eq_refl eq_refl). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & gen' & rwcur' & -> & HJc & HP & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
exists r, gen', rwcur'. repeat (split; [assumption|]). exact HB2.
- intros a Ha. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hba). split; [exact (HFPin b n a Hbn Hba) | apply HFPlow; exact (HFPin b n a Hbn Hba)]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2)).
exists L2, A2, regs2, mem2, md2, r, gen', rwcur'. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
repeat (split; [assumption|]).
pose proof HJc2 as (_ & _ & Hhi2 & _). rewrite Hsp in Hhi2. exact Hhi2. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & gen' & rwcur' & -> & HJ2 & HP2 & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hhi2, HJ2, Hr10, Hat2.
set (s' := flush_upd s 2 gen' rwcur') in *.
assert (Hvals' : cgif_vals s' = cgif_vals s) by (subst s'; apply cgif_vals_flush_upd).
assert (Hblk' : cgif_blocks g s' N = cgif_blocks g s N) by (subst s'; apply flush_upd_blocks; rewrite Hlen; lia).
assert (HB2' : Permutation (blocks L2 A2) (cgif_blocks g s' N ++ rest)) by (rewrite Hblk'; exact HB2).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
destruct (cgif_geom L2 A2 mem2 md2 g s' N rest HH2 HB2') as ((Hr0' & Hr1' & Hrg') & Hfgeom' & _).
pose proof Hat2 as (Hobj2 & Hraw2 & Hfrs2). rewrite Hvals' in Hobj2.
destruct (obj_cgif_parts mem2 g s Hobj2) as (H15' & Hcur' & _ & Hih' & _).
jafter_call_keep HS 55%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | unfold FLUSH_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq57. cbn [ms_regs mkst] in Hq57. rewrite Hr10 in Hq57. symmetry in Hq57.
add_region HS cl_R2.
2:{ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE o HH2 Hgin2 ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur']. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih']. }
apply Forall_nil. }
2:{ unfold cl_R2. cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. repeat split; lia. }
add_region HS cl_R1.
2:{ unfold cl_R1. eapply (region_ok_obj_gen ubs2segs _ mem2 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[ew_havocA; exact HU8 | lia | lia | exact H15' | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. assert (Hlj : (j < length (vals15 s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
change (length (vals15 s)) with 15%nat in Hlj.
rewrite ew_havoc_old by lia. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj | exact Hlj]. }
2:{ unfold cl_R1, cl_R2. cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. repeat split; lia. }
assert (TR2 : forall m', (forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs2segs m' a = mbyte ubs2segs mem2 a) ->
obj_at ubs2segs m' (cg_raw s') LAY_Raw (raw_vals g s') /\ (forall f, In (Some f) (cg_frames s') -> obj_at ubs2segs m' (fr_ptr f) LAY_Frame (frame_vals f))).
{ intros m' Hm'. split.
- eapply obj_at_transport_range; [exact Hraw2 | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply Hm'; lia.
- intros f Hin. destruct (Hfgeom' f Hin) as (F0 & F1 & F2). eapply obj_at_transport_range; [exact (Hfrs2 f Hin) | exact (proj1 LAY_Frame_ok)|]. intros i Hi. apply Hm'; lia. }
assert (HFPin' : forall b n a, In (b, n) (cgif_blocks g s' N) -> b <= a < b + n -> inFP FP a) by (rewrite Hblk'; exact HFPin).
jrun LAWS ubs2tbl_ok HS HJ2. { wr_any HU2 HU8 Hgin2 HFPin. }
jbranch ubs2tbl HS; clear Hc.
+
jrun_to LAWS ubs2tbl_ok HS HJ2 CL_CLEAN. { wr_any HU2 HU8 Hgin2 HFPin. }
cgif_obj_low_at 0%nat 1%nat HS HU8 HXn Rg s 59%nat.
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ [?cc; _]) |- _ => rename Hx into Hobj3; set (c := cc) in Hobj3 end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR2 (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia))) as [Hraw3 Hfrs3] end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_clean API IMG L A mem md regs0 rg L2 A2 mm md2 g N (set_cur s' c) rest FP) end;
[ exact HJ2 | exact Hra0 | exact Htp0 | exact Hal16 | exact HFPin' | exact HFPlow | | apply set_cur_wf; exact Hwf2 | exact HB2' | | | | | ].
* split; [| split; [exact Hraw3 | exact Hfrs3]]. rewrite cgif_vals_set_cur. unfold vals15. rewrite Hvals'. change (cg_ihead s') with (cg_ihead s). exact Hobj3.
* unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 48 + (48 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 40 (SOff 49 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 32 (SOff 50 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 24 (SOff 51 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 16 (SOff 52 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 8 (SOff 53 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW53, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 0 (SOff 54 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW54, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
* reg_nowF HS ltac:(rewrite HU2; reflexivity).
* reg_nowF HS ltac:(rewrite HU8; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
* unfold cl_untouched; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
+
jrun_to LAWS ubs2tbl_ok HS HJ2 CL_CLEAN. { wr_any HU2 HU8 Hgin2 HFPin. }
cgif_obj_now_at 0%nat 1%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj3 end. rewrite <- cgif_vals_split, <- Hvals' in Hobj3.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR2 (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia))) as [Hraw3 Hfrs3] end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_clean API IMG L A mem md regs0 rg L2 A2 mm md2 g N s' rest FP) end;
[ exact HJ2 | exact Hra0 | exact Htp0 | exact Hal16 | exact HFPin' | exact HFPlow | | exact Hwf2 | exact HB2' | | | | | ].
* split; [exact Hobj3 | split; [exact Hraw3 | exact Hfrs3]].
* unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 48 + (48 - dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 40 (SOff 49 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW49, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 32 (SOff 50 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW50, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 24 (SOff 51 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW51, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 16 (SOff 52 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW52, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 8 (SOff 53 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW53, Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat 0 (SOff 54 0) (sp0 - 48) _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW54, Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
* reg_nowF HS ltac:(rewrite HU2; reflexivity).
* reg_nowF HS ltac:(rewrite HU8; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
* unfold cl_untouched; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
Qed.
Definition ss_close0 : sstate :=
mkSS CLOSE sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 88 0 0 (obj_chunks_gen LAY15 32 lits15) ;
YQ0b.mkRegion (Some 10%nat) 88 96 88 92 [mkChunk 88 (CVal 4 (SOff 47 0)); mkChunk 92 (CVal 4 (SOff 48 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + CLOSE_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(47%nat, mkAF 0 4294967295 0); (48%nat, mkAF 0 4294967295 0) ] [] []).
Theorem ubs2_cgif_close : close_spec API.
Proof.
intros L A regs mem md g s N rest HPRE Hid G10 Hat Hwf HB.
pose proof HPRE as (HH & Hra0 & Hst & Htp0 & Herr).
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof Hwf as (Hlen & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
assert (Hspm : (sp0 - 48) mod 16 = 0) by (replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (FP := blocks_fp (cgif_blocks g s N)).
assert (HFPin : forall b n a, In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP FP a) by (intros b n a Hbn Ha; apply (cgif_fp_in g s N b n a Hbn Ha)).
assert (HFPlow : forall a, inFP FP a -> a < alloc_ceiling).
{ intros a Ha. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hba).
destruct (blocks_range _ _ LAWS L A mem md b n HH ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; left; exact Hbn)). lia. }
assert (Hgin : In (g, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (cgif_geom L A mem md g s N rest HH HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := Ereg regs (map (Z_to_bv 64) (cgif_vals s) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error (cgif_vals s) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HXn : forall n j v, n = (32 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) by (intros n j v -> Hj; apply HX; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = g) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
destruct (obj_cgif_parts mem g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok ubs2segs E ss_close0 (mkst regs (Z_to_bv 64 CLOSE) mem (seg_rom ubs2segs))).
{ unfold ss_close0. replace ubs2_A_cgif_close with CLOSE by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack ubs2segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ eapply (region_ok_obj_gen ubs2segs _ mem 10 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU10 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L A mem md g CGIF_SIZE o HH Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10. repeat split; lia.
- cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU10, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
pose proof (journal_init ubs2_msyms MR CLOSE_STK FP L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 CLOSE) mem (seg_rom ubs2segs))) in HJ. fold sp0 in HJ.
assert (TR : forall m', (forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs2segs m' a = mbyte ubs2segs mem a) ->
obj_at ubs2segs m' (cg_raw s) LAY_Raw (raw_vals g s) /\ (forall f, In (Some f) (cg_frames s) -> obj_at ubs2segs m' (fr_ptr f) LAY_Frame (frame_vals f))).
{ intros m' Hm'. split.
- eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply Hm'; lia.
- intros f Hin. destruct (Hfgeom f Hin) as (F0 & F1 & F2). eapply obj_at_transport_range; [exact (Hfrs f Hin) | exact (proj1 LAY_Frame_ok)|]. intros i Hi. apply Hm'; lia. }
jrun LAWS ubs2tbl_ok HS HJ. { wr_any HU2 HU10 Hgin HFPin. }
jbranch ubs2tbl HS; clear Hc.
-
jrun_to LAWS ubs2tbl_ok HS HJ CL_CLEAN. { wr_any HU2 HU10 Hgin HFPin. }
cgif_obj_now_p 10%nat 1%nat 2%nat HS HU10 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw2 Hfrs2] end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_clean API IMG L A mem md regs rg L A mm md g N s rest FP) end;
[ exact HJ | exact Hra0 | exact Htp0 | exact Hal16 | exact HFPin | exact HFPlow | | exact Hwf | exact HB | | | | | ].
+ split; [exact Hobj2 | split; [exact Hraw2 | exact Hfrs2]].
+ unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-8) (SOff 1 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-16) (SOff 8 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 8%nat 8%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-24) (SOff 9 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-32) (SOff 18 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-40) (SOff 19 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-48) (SOff 20 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 20%nat 20%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ reg_not HS HE G10.
+ unfold cl_untouched; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
-
jrun LAWS ubs2tbl_ok HS HJ. { wr_any HU2 HU10 Hgin HFPin. }
jbranch ubs2tbl HS.
{ exfalso. rewrite branch_ltu_U, (U_not_atom _ 10 g), U_lit in Hc by first [lia | ew_havocA; rewrite (HE 10%nat 10%bv eq_refl); exact G10].
apply Z.ltb_lt in Hc. lia. }
clear Hc.
jrun LAWS ubs2tbl_ok HS HJ. { wr_any HU2 HU10 Hgin HFPin. }
jbranch ubs2tbl HS.
+
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ CL_LOOP. { wr_any HU2 HU10 Hgin HFPin. }
cgif_obj_now_p 10%nat 1%nat 2%nat HS HU10 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw2 Hfrs2] end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_iter2 L A mem md regs rg L A mm md g N s rest FP) end;
[ exact HJ | exact Hid | exact Hra0 | exact Htp0 | exact Hal16 | exact HFPin | exact HFPlow | | exact Hwf | exact HB | | | | | | | | ].
* split; [exact Hobj2 | split; [exact Hraw2 | exact Hfrs2]].
* unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-8) (SOff 1 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-16) (SOff 8 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 8%nat 8%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-24) (SOff 9 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-32) (SOff 18 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-40) (SOff 19 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-48) (SOff 20 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 20%nat 20%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite HU10; reflexivity).
* reg_not HS HE G10.
* reg_nowF HS ltac:(rewrite HU10; reflexivity).
* reg_nowF HS ltac:(reflexivity).
* reg_nowF HS ltac:(reflexivity).
* unfold cl_untouched; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+
rewrite branch_eq_U, (U_atom _ 33 (frame_ptr (nth 1 (cg_frames s) None))), U_lit in Hc;
[| lia | ew_havocA; apply (HXn 33%nat 1%nat _ eq_refl eq_refl) | ].
2:{ pose proof (Rg 1%nat _ eq_refl) as R33. cbn [nth snd LAY_CGIF Z.of_N] in R33. lia. }
destruct (nth 1 (cg_frames s) None) as [f1|] eqn:Hn1; [| cbn in Hc; discriminate Hc]. clear Hc.
assert (Ho1 : nth_error (cg_frames s) 1 = Some (Some f1)) by (rewrite (nth_error_nth' _ None) by lia; rewrite Hn1; reflexivity).
assert (Hf1in : In (Some f1) (cg_frames s)) by (eapply nth_error_In; exact Ho1).
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_flushFrame. { wr_any HU2 HU10 Hgin HFPin. }
jreg HS (10%bv:reg) as Hm10. jreg HS (11%bv:reg) as Hm11. jreg HS (12%bv:reg) as Hm12.
jreg HS (2%bv:reg) as Hm2. rewrite HU2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), Htp0 in Hm4. jreg HS (1%bv:reg) as Hm1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 48) by (unfold spZ; rewrite Hm2; rewrite unsigned_lit_small by lia; lia) end.
cgif_obj_now_p 10%nat 1%nat 2%nat HS HU10 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj1 end. rewrite <- cgif_vals_split in Hobj1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw1 Hfrs1] end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2 (r gen' rwcur' : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs2_A_cgif_close + 0x5c)) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 1 gen' rwcur') /\ cgif_wf (flush_upd s 1 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks g s N ++ rest) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 48 - FLUSH_STK <= x < sp0 - 48) ->
mbyte ubs2segs mem2 x = mbyte ubs2segs (ms_mem msx) x /\ (writable_at ubs2segs (ms_mem msx) x <-> writable_at ubs2segs mem2 x)))
end.
{ eapply SR_mono.
{ eapply (jcall ubs2_msyms MR) with (STK1 := FLUSH_STK) (FP1 := blocks_fp (cgif_blocks g s N))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => exists r gen' rwcur' : Z,
st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 1 gen' rwcur') /\ cgif_wf (flush_upd s 1 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks g s N ++ rest));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FLUSH_STK; lia | rewrite Hsp; unfold FLUSH_STK; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (FLUSH L A _ _ md g s N 1%nat f1 rest HPRE1 Hid); [ | | exact Hwf | left; reflexivity | exact Ho1 | | | exact HB ].
+ rewrite Hm10. ew_havocA. rewrite <- HU10. symmetry. apply Z_to_bv_bv_unsigned.
+ split; [exact Hobj1 | split; [exact Hraw1 | exact Hfrs1]].
+ rewrite Hm11. ew_havocA. rewrite (HXn 33%nat 1%nat _ eq_refl eq_refl), Hn1. reflexivity.
+ rewrite Hm12. ew_havocA. rewrite (HXn 32%nat 0%nat _ eq_refl eq_refl). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & gen' & rwcur' & -> & HJc & HP & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
exists r, gen', rwcur'. repeat (split; [assumption|]). exact HB2.
- intros a Ha. apply inFP_blocks_fp in Ha as (b & n & Hbn & Hba). split; [exact (HFPin b n a Hbn Hba) | apply HFPlow; exact (HFPin b n a Hbn Hba)]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2)).
exists L2, A2, regs2, mem2, md2, r, gen', rwcur'. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
repeat (split; [assumption|]).
pose proof HJc2 as (_ & _ & Hhi2 & _). rewrite Hsp in Hhi2. exact Hhi2. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & gen' & rwcur' & -> & HJ2 & HP2 & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hhi2, HJ2, Hr10, Hat2.
set (s' := flush_upd s 1 gen' rwcur') in *.
assert (Hvals' : cgif_vals s' = cgif_vals s) by (subst s'; apply cgif_vals_flush_upd).
assert (Hblk' : cgif_blocks g s' N = cgif_blocks g s N) by (subst s'; apply flush_upd_blocks; rewrite Hlen; lia).
assert (HB2' : Permutation (blocks L2 A2) (cgif_blocks g s' N ++ rest)) by (rewrite Hblk'; exact HB2).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
destruct (cgif_geom L2 A2 mem2 md2 g s' N rest HH2 HB2') as ((Hr0' & Hr1' & Hrg') & Hfgeom' & _).
pose proof Hat2 as (Hobj2 & Hraw2 & Hfrs2). rewrite Hvals' in Hobj2.
destruct (obj_cgif_parts mem2 g s Hobj2) as (H15' & Hcur' & _ & Hih' & _).
jafter_call_keep HS 53%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | unfold FLUSH_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 10%nat) 88 96 88 92 [mkChunk 88 (CVal 4 (SOff 47 0)); mkChunk 92 (CVal 4 (SOff 48 0))]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE o HH2 Hgin2 ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur']. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih']. }
apply Forall_nil. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU10. repeat split; lia. }
add_region HS (YQ0b.mkRegion (Some 10%nat) 0 88 0 0 (obj_chunks_gen LAY15 32 lits15)).
2:{ eapply (region_ok_obj_gen ubs2segs _ mem2 10 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[ew_havocA; exact HU10 | lia | lia | exact H15' | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. assert (Hlj : (j < length (vals15 s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
change (length (vals15 s)) with 15%nat in Hlj.
rewrite ew_havoc_old by lia. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj | exact Hlj]. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU10. repeat split; lia. }
assert (TR2 : forall m', (forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs2segs m' a = mbyte ubs2segs mem2 a) ->
obj_at ubs2segs m' (cg_raw s') LAY_Raw (raw_vals g s') /\ (forall f, In (Some f) (cg_frames s') -> obj_at ubs2segs m' (fr_ptr f) LAY_Frame (frame_vals f))).
{ intros m' Hm'. split.
- eapply obj_at_transport_range; [exact Hraw2 | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply Hm'; lia.
- intros f Hin. destruct (Hfgeom' f Hin) as (F0 & F1 & F2). eapply obj_at_transport_range; [exact (Hfrs2 f Hin) | exact (proj1 LAY_Frame_ok)|]. intros i Hi. apply Hm'; lia. }
assert (HFPin' : forall b n a, In (b, n) (cgif_blocks g s' N) -> b <= a < b + n -> inFP FP a) by (rewrite Hblk'; exact HFPin).
jrun LAWS ubs2tbl_ok HS HJ2. { wr_any HU2 HU10 Hgin2 HFPin. }
jbranch ubs2tbl HS; clear Hc.
*
jrun_to LAWS ubs2tbl_ok HS HJ2 CL_CLEAN. { wr_any HU2 HU10 Hgin2 HFPin. }
cgif_obj_low_p 10%nat 0%nat 1%nat HS HU10 HXn Rg s 57%nat.
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ [?cc; _]) |- _ => rename Hx into Hobj3; set (c := cc) in Hobj3 end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR2 (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw3 Hfrs3] end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_clean API IMG L A mem md regs rg L2 A2 mm md2 g N (set_cur s' c) rest FP) end;
[ exact HJ2 | exact Hra0 | exact Htp0 | exact Hal16 | exact HFPin' | exact HFPlow | | apply set_cur_wf; exact Hwf2 | exact HB2' | | | | | ].
-- split; [| split; [exact Hraw3 | exact Hfrs3]]. rewrite cgif_vals_set_cur. unfold vals15. rewrite Hvals'. change (cg_ihead s') with (cg_ihead s). exact Hobj3.
-- unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-8) (SOff 1 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-16) (SOff 8 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 8%nat 8%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-24) (SOff 9 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-32) (SOff 18 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-40) (SOff 19 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-48) (SOff 20 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 20%nat 20%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
-- reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
-- reg_nowF HS ltac:(rewrite HU10; reflexivity).
-- reg_not HS HE G10.
-- unfold cl_untouched; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
*
jrun_to LAWS ubs2tbl_ok HS HJ2 CL_LOOP. { wr_any HU2 HU10 Hgin2 HFPin. }
cgif_obj_now_p 10%nat 0%nat 1%nat HS HU10 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj3 end. rewrite <- cgif_vals_split, <- Hvals' in Hobj3.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR2 (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw3 Hfrs3] end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_iter2 L A mem md regs rg L2 A2 mm md2 g N s' rest FP) end;
[ exact HJ2 | exact Hid2 | exact Hra0 | exact Htp0 | exact Hal16 | exact HFPin' | exact HFPlow | | exact Hwf2 | exact HB2' | | | | | | | | ].
-- split; [exact Hobj3 | split; [exact Hraw3 | exact Hfrs3]].
-- unfold cl_saved_ok;
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia end;
[ eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-8) (SOff 1 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-16) (SOff 8 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 8%nat 8%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-24) (SOff 9 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-32) (SOff 18 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-40) (SOff 19 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
| eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-48) (SOff 20 0) sp0 _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 20%nat 20%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range'] ].
-- reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
-- reg_nowF HS ltac:(rewrite HU10; reflexivity).
-- reg_not HS HE G10.
-- reg_nowF HS ltac:(rewrite HU10; reflexivity).
-- reg_nowF HS ltac:(reflexivity).
-- reg_nowF HS ltac:(reflexivity).
-- unfold cl_untouched; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Qed.
Theorem ubs2_close_spec : close_spec API.
Proof. exact ubs2_cgif_close. Qed.
End S.
End h.
