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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r
UI1w UI4l UI21 UI2m UI5o UI5l YI6b UI5n
UI20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 UI3u UI22 YI5a UI23 YI05 YI18 YI0o UI2n YI0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI1x YI0c UI1z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cgif_vals_flush_upd : forall s i gen' rwcur', cgif_vals (flush_upd s i gen' rwcur') = cgif_vals s.
Proof using. intros. unfold cgif_vals. rewrite !flush_upd_frames_shape. reflexivity. Qed.
Lemma frames_blocks_flush_upd : forall N s i gen' rwcur', (i < length (cg_frames s))%nat ->
frames_blocks N (cg_frames (flush_upd s i gen' rwcur')) = frames_blocks N (cg_frames s).
Proof using.
intros N s i gen' rwcur' Hi. pose proof (flush_upd_blocks 0 s N i gen' rwcur' Hi) as H.
unfold cgif_blocks in H. injection H as H. apply app_inv_head in H. exact H.
Qed.
Lemma length_frames_flush_upd : forall s i gen' rwcur', length (cg_frames (flush_upd s i gen' rwcur')) = length (cg_frames s).
Proof using. intros. rewrite flush_upd_wf_frames. apply length_list_set. Qed.
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
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_iter2 : sstate :=
mkSS CL_LOOP (sr_set (sr_set (sr_set sr_atoms 18%bv (SOff 8 16)) 19%bv (SLit 16)) 20%bv (SLit 24))
[ YP09.mkRegion (Some 2%nat) 0 48 0 48 cl_saved ; cl_R1 ; cl_R2 ]
None (mkFacts cl_facts [] []).
End e.
Ltac cgif_obj_now_p p i1 i2 HS HU8 HXn Rg s cur ecur tcur :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch type of HU8 with bv_unsigned _ = ?g =>
assert (obj_at ubs0segs (ms_mem msc) g LAY_CGIF (vals15 s ++ [cur; cg_ihead s]));
[ apply obj_cgif_join;
[ eapply (st_obj_at ubs0segs _ _ _ i1 _ p g LAY15 (vals15 s) 32 lits15 HS eq_refl eq_refl ltac:(ew_havocA; exact HU8));
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
eapply (st_chunk_val ubs0segs _ _ _ i2 _ p 88 4%N ecur _ cur HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | tcur | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption
| replace (g + 92) with (bv_unsigned (ew Ec p) + 92) by (ew_havocA; rewrite HU8; reflexivity);
eapply (st_chunk_val ubs0segs _ _ _ i2 _ p 92 4%N (SOff 48 0) _ (cg_ihead s) HS);
[reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption ]
| ] end end.
Ltac cgif_obj_low_p p i1 i2 HS HU8 HXn Rg s k :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch type of HU8 with bv_unsigned _ = ?g =>
assert (obj_at ubs0segs (ms_mem msc) g LAY_CGIF (vals15 s ++ [U Ec (SOff k 0) mod 2 ^ 32; cg_ihead s]));
[ apply obj_cgif_join;
[ eapply (st_obj_at ubs0segs _ _ _ i1 _ p g LAY15 (vals15 s) 32 lits15 HS eq_refl eq_refl ltac:(ew_havocA; exact HU8));
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
eapply (st_chunk_val ubs0segs _ _ _ i2 _ p 92 4%N (SOff 48 0) _ (cg_ihead s) HS);
[reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4%N)) with (2 ^ 32); assumption | cbn; lia]
| assumption ]
| ] end end.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Hypothesis FCLOSE : fclose_spec_res ubs0_msyms MR ubs0_A_fclose.
Hypothesis FLUSHX : flushX_spec API.
Lemma cgif_geom : forall L A m md g s N rest,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) ->
(4096 <= cg_raw s /\ cg_raw s + RAW_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= cg_raw s \/ cg_raw s + RAW_SIZE <= g)) /\
(forall f, In (Some f) (cg_frames s) -> 4096 <= fr_ptr f /\ fr_ptr f + FRAME_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= g)) /\
(4096 <= g /\ g + CGIF_SIZE <= alloc_ceiling /\ g mod 16 = 0).
Proof using LAWS.
intros L A m md g s N rest HH HB.
assert (Hsub : forall x, In x (cgif_blocks0 g s N) -> In x (blocks L A)).
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
Definition cl_vals (mem : word -> option byte) (s : cgif_st) (N : Z) (GPAL : list Z) (q1 q2 : option YO07.frame) : Prop :=
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) /\
oframe_relb false mem N (nth 1 (cg_frames s) None) q1 /\
oframe_relb true mem N (nth 2 (cg_frames s) None) q2.
Definition cl_vblocks (s : cgif_st) (N : Z) : list (Z * Z) :=
pal_blocks s ++ flat_map (fun o => match o with Some f => (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) | None => [] end) (cg_frames s).
Lemma cl_vblocks_in0 : forall g s N x, In x (cl_vblocks s N) -> In x (cgif_blocks0 g s N).
Proof using.
intros g s N x Hx. unfold cl_vblocks in Hx. unfold cgif_blocks0. right. right. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right].
unfold frames_blocks. apply in_flat_map in Hx as (o & Ho & Hx). apply in_flat_map. exists o. split; [exact Ho|].
destruct o as [f|]; [| exact Hx]. unfold frame_blocks. right. exact Hx.
Qed.
Lemma cl_frame_relb_kept : forall wg mem mem' N f fr,
(forall k, 0 <= k < N -> mbyte ubs0segs mem' (fr_img f + k) = mbyte ubs0segs mem (fr_img f + k)) ->
(Z.land (fr_attr f) 1 <> 0 -> forall k, 0 <= k < 3 * fr_nlp f -> mbyte ubs0segs mem' (fr_lpal f + k) = mbyte ubs0segs mem (fr_lpal f + k)) ->
frame_relb wg mem N f fr -> frame_relb wg mem' N f fr.
Proof using.
intros wg mem mem' N f fr Ki Kl (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [| split; [exact Hil|]].
- eapply garr8_frame; [exact Hi|]. intros a Ha. replace a with (fr_img f + (a - fr_img f)) by lia. apply Ki. lia.
- intros Hz. destruct (Hl Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (fr_lpal f + (a - fr_lpal f)) by lia. apply (Kl Hz). lia.
Qed.
Lemma cl_vals_kept : forall mem mem' s N GPAL q1 q2,
(forall a n k, In (a, n) (cl_vblocks s N) -> 0 <= k < n -> mbyte ubs0segs mem' (a + k) = mbyte ubs0segs mem (a + k)) ->
cl_vals mem s N GPAL q1 q2 -> cl_vals mem' s N GPAL q1 q2.
Proof using.
intros mem mem' s N GPAL q1 q2 K (R4 & F1 & F2).
assert (FR : forall wg j q, oframe_relb wg mem N (nth j (cg_frames s) None) q -> oframe_relb wg mem' N (nth j (cg_frames s) None) q).
{ intros wg j q H. destruct (nth j (cg_frames s) None) as [f|] eqn:Hn; destruct q as [fr|]; cbn [oframe_relb] in H |- *; try exact H.
assert (Hin : In (Some f) (cg_frames s)).
{ rewrite <- Hn. apply nth_In. destruct (Nat.lt_ge_cases j (length (cg_frames s))) as [Hl|Hl]; [exact Hl|]. rewrite (nth_overflow _ _ Hl) in Hn. discriminate Hn. }
apply (cl_frame_relb_kept wg mem mem' N f fr); [| | exact H].
- intros k Hk. apply (K (fr_img f) N k); [| exact Hk]. unfold cl_vblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
- intros Hz k Hk. apply (K (fr_lpal f) (3 * fr_nlp f) k); [| exact Hk]. unfold cl_vblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin|].
right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]. }
split; [| split; [apply FR; exact F1 | apply FR; exact F2]].
intros Hz. destruct (R4 Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (cg_pal s + (a - cg_pal s)) by lia. apply (K (cg_pal s) (3 * cg_ngp s)); [| lia]. unfold cl_vblocks. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
Qed.
Lemma oframe_relb_keptV : forall mem mem' s N wg j q,
(forall a n k, In (a, n) (cl_vblocks s N) -> 0 <= k < n -> mbyte ubs0segs mem' (a + k) = mbyte ubs0segs mem (a + k)) ->
oframe_relb wg mem N (nth j (cg_frames s) None) q -> oframe_relb wg mem' N (nth j (cg_frames s) None) q.
Proof using.
intros mem mem' s N wg j q K H. destruct (nth j (cg_frames s) None) as [f|] eqn:Hn; destruct q as [fr|]; cbn [oframe_relb] in H |- *; try exact H.
assert (Hin : In (Some f) (cg_frames s)).
{ rewrite <- Hn. apply nth_In. destruct (Nat.lt_ge_cases j (length (cg_frames s))) as [Hl|Hl]; [exact Hl|]. rewrite (nth_overflow _ _ Hl) in Hn. discriminate Hn. }
apply (cl_frame_relb_kept wg mem mem' N f fr); [| | exact H].
- intros k Hk. apply (K (fr_img f) N k); [| exact Hk]. unfold cl_vblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
- intros Hz k Hk. apply (K (fr_lpal f) (3 * fr_nlp f) k); [| exact Hk]. unfold cl_vblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin|].
right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity].
Qed.
Lemma gpal_keptV : forall mem mem' s N GPAL,
(forall a n k, In (a, n) (cl_vblocks s N) -> 0 <= k < n -> mbyte ubs0segs mem' (a + k) = mbyte ubs0segs mem (a + k)) ->
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) ->
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs mem' (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s).
Proof using.
intros mem mem' s N GPAL K R4 Hz. destruct (R4 Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (cg_pal s + (a - cg_pal s)) by lia. apply (K (cg_pal s) (3 * cg_ngp s)); [| lia]. unfold cl_vblocks. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
Qed.
Lemma cl_vblocks_geom : forall L A m md g s N rest a n,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) -> In (a, n) (cl_vblocks s N) ->
In (a, n) (blocks L A) /\ 4096 <= a /\ a + n <= alloc_ceiling /\ (g + CGIF_SIZE <= a \/ a + n <= g).
Proof using LAWS.
intros L A m md g s N rest a n HH HB Hx.
pose proof (cl_vblocks_in0 g s N _ Hx) as H0.
assert (Hl : In (a, n) (blocks L A)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; left; exact H0).
destruct (blocks_range _ _ LAWS L A m md a n HH Hl) as [R0 R1]. split; [exact Hl|]. split; [exact R0|]. split; [exact R1|].
assert (Hy : In (a, n) (pal_blocks s ++ frames_blocks N (cg_frames s))).
{ unfold cl_vblocks in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right].
apply in_flat_map in Hx as (o & Ho & Hx). unfold frames_blocks. apply in_flat_map. exists o. split; [exact Ho|]. destruct o as [f|]; [| exact Hx]. unfold frame_blocks. right. exact Hx. }
pose proof (heap_sep_perm _ _ LAWS L A m md (g, CGIF_SIZE) ((cg_raw s, RAW_SIZE) :: (pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest) (a, n) HH HB ltac:(right; apply in_app_iff; left; exact Hy)) as Hs.
cbn [fst snd] in Hs. exact Hs.
Qed.
Lemma vblocks_TR : forall L A m md m1 m2 g s N rest,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) ->
(forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs0segs m2 a = mbyte ubs0segs m1 a) ->
forall a n k, In (a, n) (cl_vblocks s N) -> 0 <= k < n -> mbyte ubs0segs m2 (a + k) = mbyte ubs0segs m1 (a + k).
Proof using LAWS.
intros L A m md m1 m2 g s N rest HH HB K a n k Hin Hk. destruct (cl_vblocks_geom L A m md g s N rest a n HH HB Hin) as (_ & R0 & R1 & Rs). apply K; unfold CGIF_SIZE in *; lia.
Qed.
Lemma cl_vals_low : forall L A m md m1 m2 g s N rest GPAL q1 q2,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) ->
(forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs0segs m2 a = mbyte ubs0segs m1 a) ->
cl_vals m1 s N GPAL q1 q2 -> cl_vals m2 s N GPAL q1 q2.
Proof using LAWS.
intros L A m md m1 m2 g s N rest GPAL q1 q2 HH HB K HV. apply (cl_vals_kept m1 m2 s N GPAL q1 q2); [| exact HV].
intros a n k Hin Hk. destruct (cl_vblocks_geom L A m md g s N rest a n HH HB Hin) as (_ & R0 & R1 & Rs). apply K; unfold CGIF_SIZE in *; lia.
Qed.
Lemma sink_at_low : forall L A m md m1 m2 g f S mdl,
heap_ok MR L A m md -> In (g, CGIF_SIZE) (blocks L A) -> In (f, FILE_BLOCK) (blocks L A) ->
(forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs0segs m2 a = mbyte ubs0segs m1 a) ->
sink_at ubs0_msyms m1 mdl f S -> sink_at ubs0_msyms m2 mdl f S.
Proof using IMG LAWS.
intros L A m md m1 m2 g f S mdl HH Hg Hf K HS. pose proof (proj1 alloc_ceiling_val) as Hac.
apply (sink_at_frame ubs0_msyms m1 m2 mdl f S); [| exact HS]. intros a Ha.
destruct (blocks_range _ _ LAWS L A m md f FILE_BLOCK HH Hf) as [F0 F1].
destruct (blocks_range _ _ LAWS L A m md g CGIF_SIZE HH Hg) as [G0 G1].
destruct Ha as [Ha|Ha].
- pose proof (heap_sep_in2 _ _ LAWS L A m md (g, CGIF_SIZE) (f, FILE_BLOCK) HH Hg Hf) as Hd. cbn [fst snd] in Hd.
unfold CGIF_SIZE, FILE_BLOCK in *. destruct Hd as [Hd|Hd]; [intros E; injection E as E1 E2; lia | apply K; lia | apply K; lia].
- pose proof (ubs0_env_addr_range a Ha) as Hr.
assert (Hng : ~ (g <= a < g + CGIF_SIZE)).
{ intros Hin. apply (proj1 (blocks_In _ _ _ _)) in Hg as (q & Hq & Hqin). destruct (skl_env ubs0_msyms a Ha) as (Himg1 & _).
apply (il_blocks IMG L A m md q CGIF_SIZE (a - g) (proj1 HH) Hqin ltac:(lia)). rewrite Hq. replace (g + (a - g)) with a by lia. exact Himg1. }
apply K; unfold CGIF_SIZE in *; lia.
Qed.
Definition cl_brb (o : option frame_st) (b : rbound) : rbound := match o with Some _ => flush_rb b | None => b end.
Definition nsome (os : list (option frame_st)) : Z := fold_right (fun o k => match o with Some _ => k + 1 | None => k end) 0 os.
Lemma frs_rb_eq : forall N os b,
frs_rb N os b = RB (rb_bytes b - nsome os * prN N) (rb_cnt b - nsome os * (if MMAP_THRESHOLD <? N then 1 else 0)) (rb_hand b) (rb_brk b).
Proof using.
intros N os. induction os as [|o os IH]; intros b.
- cbn. destruct b; cbn; f_equal; lia.
- cbn [frs_rb fold_left]. change (fold_left (fun b' o' => fr_rb N o' b') os (fr_rb N o b)) with (frs_rb N os (fr_rb N o b)). rewrite IH.
cbn [nsome fold_right]. change (fold_right (fun o' k => match o' with Some _ => k + 1 | None => k end) 0 os) with (nsome os).
destruct o as [f|]; cbn [fr_rb]; [| f_equal; lia].
unfold rb_free, prN. destruct (MMAP_THRESHOLD <? N); cbn; f_equal; lia.
Qed.
Lemma nsome_range3 : forall o0 o1 o2, 0 <= nsome [o0; o1; o2] <= 3.
Proof using. intros [a|] [b|] [c|]; cbn; lia. Qed.
Lemma nsome_nonneg : forall os, 0 <= nsome os.
Proof using. unfold nsome. induction os as [|[f|] os IH]; cbn; lia. Qed.
Lemma frs_rb_close : forall N os b b' k q,
0 <= N -> 0 <= k <= CLOSE_K -> rb_le b' (rb_acc b k 0) -> nsome os = q ->
rb_le (frs_rb N os b') (close_rb b N q).
Proof using.
intros N os b b' k q HN Hk (L1 & L2 & L3 & L4) Hq. rewrite frs_rb_eq. subst q.
pose proof (nsome_nonneg os) as Hn. pose proof (prN_nonneg N HN) as Hp.
unfold close_rb, rb_acc, rb_le in *. cbn in *. unfold CLOSE_K, FLUSH_K, RAWADD_K, LZW_K, MMAX, PGSZ in *.
destruct (MMAP_THRESHOLD <? N); nia.
Qed.
Lemma flush_rb_acc : forall b, flush_rb b = rb_acc b FLUSH_K 0.
Proof using. intros b. reflexivity. Qed.
Lemma flush_rb_acc2 : forall b, flush_rb (flush_rb b) = rb_acc b CLOSE_K 0.
Proof using. intros b. unfold flush_rb. rewrite rb_acc_acc. unfold CLOSE_K. f_equal; lia. Qed.
Lemma close_room_flush1 : forall b N, 0 <= N -> close_room b N -> flush_room b N.
Proof using.
intros b N HN HR. unfold close_room, flush_room in *. eapply room_mono; [| | exact HR]; [| unfold flush_maxreq, rawadd_maxreq, lzw_maxreq; lia].
apply rb_acc_mono; [apply rb_le_refl | unfold CLOSE_K, FLUSH_K, RAWADD_K, LZW_K; lia | lia].
Qed.
Lemma close_room_flush2 : forall b N, close_room b N -> flush_room (flush_rb b) N.
Proof using. intros b N HR. unfold close_room, flush_room, flush_rb in *. rewrite rb_acc_acc. unfold CLOSE_K in HR. replace (FLUSH_K + FLUSH_K) with (2 * FLUSH_K) by lia. exact HR. Qed.
Lemma rc_int_range : forall v, 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= rc_int v < 2 ^ 31.
Proof using. intros v Hv. unfold rc_int. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma rc_int_mod32 : forall c, - 2 ^ 31 <= c < 2 ^ 31 -> rc_int (c mod 2 ^ 32) = c.
Proof using.
intros c Hc. unfold rc_int. destruct (Z_lt_le_dec c 0).
- replace (c mod 2 ^ 32) with (c + 2 ^ 32) by (symmetry; rewrite <- (Z.mod_add c 1 (2 ^ 32)) by lia; apply Z.mod_small; lia).
destruct (Z.ltb_spec (c + 2 ^ 32) (2 ^ 31)); lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec c (2 ^ 31)); lia.
Qed.
Lemma reg_of_code : forall r code, 0 <= r < 2 ^ 64 -> - 2 ^ 63 <= code < 2 ^ 63 -> Z_to_bv 64 r = Z_to_bv 64 code -> r = code mod 2 ^ 64.
Proof using.
intros r code Hr Hc E. rewrite <- (Z_to_bv64_mod code) in E. apply (f_equal bv_unsigned) in E.
rewrite !unsigned_lit_small in E by (try exact Hr; apply Z.mod_pos_bound; lia). exact E.
Qed.
Lemma code_zero_iff : forall r code, 0 <= r < 2 ^ 64 -> - 2 ^ 63 <= code < 2 ^ 63 -> Z_to_bv 64 r = Z_to_bv 64 code -> (r = 0 <-> code = 0).
Proof using.
intros r code Hr Hc E. rewrite (reg_of_code r code Hr Hc E). split; intros H.
- pose proof (Z.div_mod code (2 ^ 64) ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
assert (code / 2 ^ 64 = 0) by lia. rewrite D. lia.
- subst code. reflexivity.
Qed.
Lemma flush_upd1_frames : forall s gen rw o0 f1 o2, cg_frames s = [o0; Some f1; o2] ->
cg_frames (flush_upd s 1 gen rw) = [o0; Some (set_fr_gen f1 gen); o2].
Proof using. intros s gen rw o0 f1 o2 Hfs. rewrite flush_upd_wf_frames, Hfs. reflexivity. Qed.
Lemma flush_upd2_frames : forall s gen rw o0 o1 f2, cg_frames s = [o0; o1; Some f2] ->
cg_frames (flush_upd s 2 gen rw) = [o0; o1; Some (set_fr_gen f2 gen)].
Proof using. intros s gen rw o0 o1 f2 Hfs. rewrite flush_upd_wf_frames, Hfs. reflexivity. Qed.
Lemma frame_relb_set_gen : forall m N f fr gen, frame_relb true m N f fr -> frame_relb false m N (set_fr_gen f gen) fr.
Proof using. intros m N f fr gen (A1 & A2 & H). split; [exact A1|]. split; [exact I | exact H]. Qed.
Lemma occ_count : forall (o : option frame_st) (q : option YO07.frame), (o = None <-> q = None) ->
match q with Some _ => 1 | None => 0 end = match o with Some _ => 1 | None => 0 end.
Proof using. intros [f|] [fr|] [H1 H2]; try reflexivity; [discriminate (H2 eq_refl) | discriminate (H1 eq_refl)]. Qed.
Lemma nsome_flush_upd : forall s i gen rw, nsome (cg_frames (flush_upd s i gen rw)) = nsome (cg_frames s).
Proof using.
intros s i gen rw. rewrite flush_upd_wf_frames. unfold nsome. revert i. generalize (cg_frames s) as l.
induction l as [|o l IH]; intros [|i]; cbn; try reflexivity.
- destruct o; reflexivity.
- rewrite IH. reflexivity.
Qed.
Lemma cl_flush_upd_blocks0 : forall g s N i gen' rwcur', (i < length (cg_frames s))%nat -> cgif_blocks0 g (flush_upd s i gen' rwcur') N = cgif_blocks0 g s N.
Proof using.
intros g s N i gen' rwcur' Hi. pose proof (flush_upd_blocks g s N i gen' rwcur' Hi) as H. unfold cgif_blocks in H. unfold cgif_blocks0.
assert (H1 : forall (a b c : Z * Z) l l', a :: b :: c :: l = a :: b :: c :: l' -> l = l') by (intros a b c l l' E0; injection E0 as E1; exact E1).
apply H1 in H. cbn [cg_raw cg_file flush_upd] in H |- *. rewrite H. reflexivity.
Qed.
Lemma qcount_nsome : forall s gs o0 o1 o2, cg_frames s = [o0; o1; o2] -> cgif_occ s gs -> qcount gs = nsome [o0; o1; o2].
Proof using.
intros s gs o0 o1 o2 Hfs (X0 & X1 & X2). rewrite Hfs in X0, X1, X2. cbn [nth] in X0, X1, X2. unfold qcount.
rewrite (occ_count _ _ X0), (occ_count _ _ X1), (occ_count _ _ X2). destruct o0, o1, o2; reflexivity.
Qed.
Lemma vblock_sep_frame : forall L A m md g s N rest f1 a n,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) -> In (Some f1) (cg_frames s) ->
In (a, n) (cl_vblocks s N) -> fr_ptr f1 + FRAME_SIZE <= a \/ a + n <= fr_ptr f1.
Proof using LAWS.
intros L A m md g s N rest f1 a n HH HB Hf1 Hx.
apply in_split in Hf1 as (fs1 & fs2 & Hfs).
set (lp := if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]).
set (l1 := (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N fs1).
set (l2 := ((fr_img f1, N) :: lp ++ frames_blocks N fs2) ++ rest).
assert (HE : cgif_blocks0 g s N ++ rest = l1 ++ (fr_ptr f1, FRAME_SIZE) :: l2).
{ unfold cgif_blocks0. rewrite Hfs. unfold frames_blocks. rewrite flat_map_app. cbn [flat_map]. subst l1 l2 lp. unfold frames_blocks, frame_blocks.
cbn [app]. rewrite <- !app_assoc. cbn [app]. rewrite <- !app_assoc. reflexivity. }
rewrite HE in HB.
pose proof (heap_sep_perm _ _ LAWS L A m md (fr_ptr f1, FRAME_SIZE) (l1 ++ l2) (a, n) HH ltac:(eapply Permutation_trans; [exact HB | apply Permutation_sym; apply Permutation_middle])) as Hs.
cbn [fst snd] in Hs. apply Hs. clear Hs HB HE.
unfold cl_vblocks in Hx. rewrite Hfs in Hx. rewrite flat_map_app in Hx. cbn [flat_map] in Hx.
apply in_app_iff. apply in_app_iff in Hx as [Hx|Hx].
- left. subst l1. right. right. apply in_app_iff. left. exact Hx.
- apply in_app_iff in Hx as [Hx|Hx].
+ left. subst l1. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map in Hx as (o & Ho & Hx). apply in_flat_map. exists o. split; [exact Ho|]. destruct o as [f|]; [| exact Hx]. unfold frame_blocks. right. exact Hx.
+ right. subst l2 lp. apply in_app_iff. left. cbn [app] in Hx.
destruct Hx as [Hx|Hx]; [left; exact Hx | right].
apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right].
unfold frames_blocks. apply in_flat_map in Hx as (o & Ho & Hx). apply in_flat_map. exists o. split; [exact Ho|]. destruct o as [f|]; [| exact Hx]. unfold frame_blocks. right. exact Hx.
Qed.
Lemma vblocks_kept_flush : forall L A m0 md0 (m m2 : word -> option byte) g s N rest fi,
heap_ok MR L A m0 md0 -> Permutation (blocks L A) (cgif_blocks0 g s N ++ (cg_file s, FILE_BLOCK) :: rest) ->
In (Some fi) (cg_frames s) ->
(forall a n k, In (a, n) (blocks L A) -> (a, n) <> (cg_file s, FILE_BLOCK) -> 0 <= k < n ->
~ (a = cg_raw s /\ 40 <= k < 44) -> ~ (a = fr_ptr fi /\ 20 <= k < 24) -> mbyte ubs0segs m2 (a + k) = mbyte ubs0segs m (a + k)) ->
forall a n k, In (a, n) (cl_vblocks s N) -> 0 <= k < n -> mbyte ubs0segs m2 (a + k) = mbyte ubs0segs m (a + k).
Proof using LAWS.
intros L A m0 md0 m m2 g s N rest fi HH HB Hfi K a n k Hx Hk.
destruct (cl_vblocks_geom L A m0 md0 g s N _ a n HH HB Hx) as (Hl & R0 & R1 & Rg).
pose proof (vblock_sep_frame L A m0 md0 g s N _ fi a n HH HB Hfi Hx) as Sf.
assert (Hy : In (a, n) (pal_blocks s ++ frames_blocks N (cg_frames s))).
{ unfold cl_vblocks in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right].
apply in_flat_map in Hx as (o & Ho & Hx). unfold frames_blocks. apply in_flat_map. exists o. split; [exact Ho|]. destruct o as [f|]; [| exact Hx]. unfold frame_blocks. right. exact Hx. }
pose proof (heap_sep_perm _ _ LAWS L A m0 md0 (cg_raw s, RAW_SIZE) ((g, CGIF_SIZE) :: (pal_blocks s ++ frames_blocks N (cg_frames s)) ++ (cg_file s, FILE_BLOCK) :: rest) (a, n) HH
ltac:(eapply Permutation_trans; [exact HB | apply perm_swap]) ltac:(right; apply in_app_iff; left; exact Hy)) as Sr. cbn [fst snd] in Sr.
pose proof (heap_sep_perm _ _ LAWS L A m0 md0 (cg_file s, FILE_BLOCK) (cgif_blocks0 g s N ++ rest) (a, n) HH
ltac:(eapply Permutation_trans; [exact HB | apply Permutation_sym; apply Permutation_middle]) ltac:(apply in_app_iff; left; apply (cl_vblocks_in0 g s N); exact Hx)) as Sfl. cbn [fst snd] in Sfl.
apply (K a n k Hl); [| exact Hk | |].
- intros E0. injection E0 as E1 E2. unfold FILE_BLOCK in *. lia.
- intros [E1 Hk']. unfold RAW_SIZE in *. lia.
- intros [E1 Hk']. unfold FRAME_SIZE in *. lia.
Qed.
Lemma cl_vals_flush1 : forall L A m0 md0 (m m2 : word -> option byte) g s N rest GPAL f1 cur1 q2 gen rw,
heap_ok MR L A m0 md0 -> Permutation (blocks L A) (cgif_blocks0 g s N ++ (cg_file s, FILE_BLOCK) :: rest) -> length (cg_frames s) = 3%nat ->
nth 1 (cg_frames s) None = Some f1 ->
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs m (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) ->
frame_relb true m N f1 cur1 -> oframe_relb true m N (nth 2 (cg_frames s) None) q2 ->
(forall a n k, In (a, n) (blocks L A) -> (a, n) <> (cg_file s, FILE_BLOCK) -> 0 <= k < n ->
~ (a = cg_raw s /\ 40 <= k < 44) -> ~ (a = fr_ptr f1 /\ 20 <= k < 24) -> mbyte ubs0segs m2 (a + k) = mbyte ubs0segs m (a + k)) ->
cl_vals m2 (flush_upd s 1 gen rw) N GPAL (Some cur1) q2.
Proof using LAWS.
intros L A m0 md0 m m2 g s N rest GPAL f1 cur1 q2 gen rw HH HB Hlen Hn1 Hgp Hf1 Hq2 K.
assert (Hf1in : In (Some f1) (cg_frames s)) by (rewrite <- Hn1; apply nth_In; rewrite Hlen; lia).
pose proof (vblocks_kept_flush L A m0 md0 m m2 g s N rest f1 HH HB Hf1in K) as KV.
assert (HV : cl_vals m2 s N GPAL (Some cur1) q2).
{ apply (cl_vals_kept m m2 s N GPAL (Some cur1) q2 KV). split; [exact Hgp|]. split; [| exact Hq2]. rewrite Hn1. cbn [oframe_relb]. eapply frame_relb_weaken. exact Hf1. }
destruct HV as (V1 & V2 & V3).
destruct (cg_frames s) as [|o0 [|o1 [|o2 [|]]]] eqn:Hfs; try (cbn in Hlen; discriminate Hlen). cbn [nth] in Hn1. subst o1.
unfold cl_vals. rewrite (flush_upd1_frames s gen rw o0 f1 o2 Hfs). cbn [cg_attr cg_pal cg_ngp flush_upd nth]. cbn [nth] in V2, V3.
split; [exact V1|]. split; [| exact V3]. cbn [oframe_relb] in V2 |- *. apply frame_relb_set_gen.
destruct V2 as (A1 & _ & Hrest). pose proof Hf1 as (_ & A2 & _). split; [exact A1|]. split; [| exact Hrest].
exact A2.
Qed.
Lemma close_postX_out : forall (regs0 : bvmap 5 word) FP L A mem md rest S bF b N q c',
close_postX API regs0 FP L A mem md rest S bF c' -> rb_le bF (close_rb b N q) ->
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR CLOSE_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
sink_none ubs0_msyms mem' md' /\
Permutation (blocks L' A') rest /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes S) /\
res_ok A' (close_rb b N q).
Proof using.
intros regs0 FP L A mem md rest S bF b N q c' (L' & A' & regs' & mem' & md' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hle.
exists L', A', regs', mem', md'. repeat (split; [assumption|]). eapply res_ok_mono; [exact Hle | exact H8].
Qed.
Lemma rc_int_zero : forall v, 0 <= v < 2 ^ 32 -> (rc_int v = 0 <-> v = 0).
Proof using. intros v Hv. unfold rc_int. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma close_iter2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (rest FP : list (Z * Z))
(S GPAL : list Z) (q1 q2 : option YO07.frame) (br : rbound),
let sp0 := spZ regs0 in
let f := cg_file s in
let G := gcfg_of s GPAL in
journal ubs0_msyms MR CLOSE_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> sp0 mod 16 = 0 -> sp0 <= 2 ^ 47 ->
(forall b n a, In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP FP a) ->
(forall a, inFP (sink_fp f) a -> inFP FP a) ->
(forall a, inFP (cgif_fp g s N) a -> inFP FP a) ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
cgif_at memc g s -> cgif_wf s N ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ (f, FILE_BLOCK) :: rest) ->
sink_at ubs0_msyms memc mdc f S -> Z.of_nat (length S) + FRAME_OUT N + 1 <= SINK_MAX ->
cl_vals memc s N GPAL q1 q2 -> rw_attr s = raw_attr_of (cg_attr s) -> 0 <= rw_cur s < 2 ^ 32 ->
res_ok Ac br -> flush_room br N ->
cl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 48) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 (2 ^ 64 - 1 - g) -> getr regs1 18 = Z_to_bv 64 (g + 16) -> getr regs1 19 = Z_to_bv 64 16 -> getr regs1 20 = Z_to_bv 64 24 ->
cl_untouched regs0 regs1 ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 CL_LOOP) memc (seg_rom ubs0segs)) mdc)
(close_postX API regs0 FP L A mem md rest (S ++ cl_bytes G (rc_int (rw_cur s)) q2 q1 ++ sink_trailer_Z) (frs_rb N (cg_frames s) (cl_brb (nth 2 (cg_frames s) None) br))).
Proof using FCLOSE FLUSHX FWRITE IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s rest FP S GPAL q1 q2 br sp0 f G HJ Hid Hra0 Htp0 Hal16 Hsp47 HFPin HFPs HFPc HFPlow Hat Hwf HB HSK HSlen HV Hrattr Rrw HRb HROOM HSV G2 G8 G9 G18 Q19 Q20 HUT.
set (rest' := (f, FILE_BLOCK) :: rest) in HB.
assert (HN0 : 0 <= N) by (pose proof Hwf as (_ & HW1 & HH1 & HNe & _); rewrite HNe; apply Z.mul_nonneg_nonneg; lia). unfold FRAME_OUT in HSlen.
assert (Hfin : In (f, FILE_BLOCK) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; right; left; reflexivity).
pose proof HUT as (G3 & G4 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof Hwf as (Hlen & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hspm : (sp0 - 48) mod 16 = 0) by (replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (cgif_geom Lc Ac memc mdc g s N rest' HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
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
pose proof HSV as (W1 & W8 & W9 & W18 & W19 & W20).
destruct (obj_cgif_parts memc g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok ubs0segs E ss_iter2 (mkst regs1 (Z_to_bv 64 CL_LOOP) memc (seg_rom ubs0segs))).
{ unfold ss_iter2. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |] | intros H0; discriminate H0 |] | intros H0; discriminate H0 |];
cbn [sv_denot]; [rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl), G8, unsigned_lit_small by lia; exact G18 | exact Q19 | exact Q20].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (cl_saved_vals regs0) j = Some w -> word_mem ubs0segs memc (sp0 - 48 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs0segs (Ereg regs1 (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) (cl_saved_vals regs0) ++ [])) memc (sp0 - 48) (mkChunk off (CVal 8 (SOff (49 + j) 0)))).
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
+ unfold cl_R1. eapply (region_ok_obj_gen ubs0segs _ memc 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU8 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE o HH0 Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- unfold cl_R1, cl_R2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU8. repeat split; lia.
- split; [| split; constructor].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU8, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl), (HE 9%nat 9%bv eq_refl), G9.
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 CL_LOOP) memc (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ. { wr_any HU2 HU8 Hgin HFPin. }
assert (TR : forall m', (forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs0segs m' a = mbyte ubs0segs memc a) ->
obj_at ubs0segs m' (cg_raw s) LAY_Raw (raw_vals g s) /\ (forall f, In (Some f) (cg_frames s) -> obj_at ubs0segs m' (fr_ptr f) LAY_Frame (frame_vals f))).
{ intros m' Hm'. split.
- eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply Hm'; lia.
- intros fq Hin. destruct (Hfgeom fq Hin) as (F0 & F1 & F2). eapply obj_at_transport_range; [exact (Hfrs fq Hin) | exact (proj1 LAY_Frame_ok)|]. intros i Hi. apply Hm'; lia. }
pose proof HV as (HVg & HVq1 & HVq2).
jbranch ubs0tbl HS.
-
rewrite branch_eq_U, (U_atom _ 34 (frame_ptr (nth 2 (cg_frames s) None))), U_lit in Hc;
[| lia | ew_havocA; apply (HXn 34%nat 2%nat _ eq_refl eq_refl) | ].
2:{ pose proof (Rg 2%nat _ eq_refl) as R34. cbn [nth snd LAY_CGIF Z.of_N] in R34. lia. }
destruct (nth 2 (cg_frames s) None) as [f2|] eqn:Hn2.
{ exfalso. destruct (Hfgeom f2 ltac:(rewrite <- Hn2; apply nth_In; rewrite Hlen; lia)) as (F0 & _). cbn [frame_ptr] in Hc. destruct (Z.eqb_spec (fr_ptr f2) 0); [lia | discriminate Hc]. }
clear Hc. destruct q2 as [cur2|]; [exact (False_ind _ HVq2)|].
cbn [cl_bytes cl_brb]. change (S ++ [] ++ sink_trailer_Z) with (S ++ sink_trailer_Z).
jrun_to LAWS ubs0tbl_ok HS HJ CL_CLEAN. { wr_any HU2 HU8 Hgin HFPin. }
cgif_obj_now_at 1%nat 2%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia))) as [Hraw2 Hfrs2] end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_clean API IMG FWRITE FCLOSE L A mem md regs0 rg Lc Ac mm mdc g N s rest FP S br) end;
[ exact HJ | exact Hra0 | exact Htp0 | exact Hal16 | exact Hsp47 | exact HFPin | exact HFPs | exact HFPlow | | exact Hwf | exact HB | | lia | | | | | | exact HRb ].
+ split; [exact Hobj2 | split; [exact Hraw2 | exact Hfrs2]].
+ lazymatch goal with |- sink_at _ ?mm _ _ _ => eapply (sink_at_low Lc Ac memc mdc memc mm g f S mdc HH0 Hgin Hfin); [| exact HSK] end.
intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia).
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
destruct q2 as [cur2|]; [| exact (False_ind _ HVq2)].
assert (Ho2 : nth_error (cg_frames s) 2 = Some (Some f2)) by (rewrite (nth_error_nth' _ None) by lia; rewrite Hn2; reflexivity).
assert (Hf2in : In (Some f2) (cg_frames s)) by (eapply nth_error_In; exact Ho2).
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_flushFrame. { wr_any HU2 HU8 Hgin HFPin. }
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
pose proof (cl_vals_low Lc Ac memc mdc memc (ms_mem msx) g s N rest' GPAL q1 (Some cur2) HH0 HB
ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia)) HV) as (HVg1 & HVq11 & HVq21);
pose proof (sink_at_low Lc Ac memc mdc memc (ms_mem msx) g f S mdc HH0 Hgin Hfin
ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia)) HSK) as HSK1 end.
rewrite Hn2 in HVq21. cbn [oframe_relb] in HVq21.
assert (HBf1 : Permutation (blocks Lc Ac) (cgif_blocks g s N ++ rest)) by (eapply Permutation_trans; [exact HB | apply Permutation_sym; apply cgif_blocks0_perm]).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2 (r gen' rwcur' code : Z) (bytes : list Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs0_A_cgif_close + 0x5c)) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 2 gen' rwcur') /\ cgif_wf (flush_upd s 2 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks0 g s N ++ rest') /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 48 - FLUSH_STK <= x < sp0 - 48) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem msx) x /\ (writable_at ubs0segs (ms_mem msx) x <-> writable_at ubs0segs mem2 x)) /\
YO07.flush_frame G (rc_int (rw_cur s)) cur2 q1 = (code, bytes) /\ Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem2 md2 f (S ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N /\ res_ok A2 (flush_rb br))
end.
{ eapply SR_mono.
{ eapply (jcall ubs0_msyms MR) with (STK1 := FLUSH_STK) (FP1 := cgif_fp g s N)
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => exists (r gen' rwcur' code : Z) (bytes : list Z),
st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 2 gen' rwcur') /\ cgif_wf (flush_upd s 2 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks0 g s N ++ rest') /\
YO07.flush_frame G (rc_int (rw_cur s)) cur2 q1 = (code, bytes) /\ Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem2 md2 f (S ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N /\ res_ok A2 (flush_rb br));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FLUSH_STK; lia | rewrite Hsp; unfold FLUSH_STK; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (FLUSHX Lc Ac _ _ mdc g s N 2%nat f2 rest S GPAL cur2 q1 br HPRE1 Hid);
[ exact HSK1 | unfold FRAME_OUT in *; lia | rewrite Hsp; lia | | | exact Hwf | right; reflexivity | exact Ho2 | | | exact HBf1 | exact HVg1 | exact HVq21 | exact HVq11 | exact Hrattr | exact HRb | exact HROOM ].
+ rewrite Hm10. ew_havocA. rewrite <- HU8. symmetry. apply Z_to_bv_bv_unsigned.
+ split; [exact Hobj1 | split; [exact Hraw1 | exact Hfrs1]].
+ rewrite Hm11. ew_havocA. rewrite (HXn 34%nat 2%nat _ eq_refl eq_refl), Hn2. reflexivity.
+ rewrite Hm12. ew_havocA. rewrite (HXn 33%nat 1%nat _ eq_refl eq_refl). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & rwcur' & -> & HJc & HP & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & (code & bytes & Hff & Hrc & Hrw & HSK2 & Hlenb) & HR2 & Hkeepv).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
exists r, (fl_gen3 G cur2 q1), rwcur', code, bytes. repeat (split; [assumption|]).
split; [eapply Permutation_trans; [exact HB2 | apply cgif_blocks0_perm]|].
repeat (split; [assumption|]). exact HR2.
- intros a Ha. split; [exact (HFPc a Ha) | apply HFPlow; exact (HFPc a Ha)]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & code & bytes & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hff & Hrc & Hrw & HSK2 & Hlenb & HR2)).
exists L2, A2, regs2, mem2, md2, r, gen', rwcur', code, bytes. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
repeat (split; [assumption|]). split; [| repeat (split; [assumption|]); exact HR2].
pose proof HJc2 as (_ & _ & Hhi2 & _). rewrite Hsp in Hhi2. exact Hhi2. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & gen' & rwcur' & code & bytes & -> & HJ2 & HP2 & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hhi2 & Hff & Hrc & Hrw & HSK2 & Hlenb & HR2). clear HJ.
assert (Hcode : - 2 ^ 31 <= code < 2 ^ 31).
{ pose proof (rc_int_range (rw_cur s) Rrw). destruct (flush_frame_code G _ _ _ _ _ Hff) as [Ec|[Ec|[Ec|Ec]]]; rewrite Ec; unfold YO07.R_ERROR, YO07.R_EINDEX, YO07.R_OK; lia. }
assert (Hfin2 : In (f, FILE_BLOCK) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2|]; apply in_app_iff; right; left; reflexivity).
replace (S ++ cl_bytes G (rc_int (rw_cur s)) (Some cur2) q1 ++ sink_trailer_Z) with ((S ++ bytes) ++ sink_trailer_Z) by (cbn [cl_bytes]; rewrite Hff; cbn [snd]; rewrite app_assoc; reflexivity).
cbn [cl_brb].
replace (frs_rb N (cg_frames s) (flush_rb br)) with (frs_rb N (cg_frames (flush_upd s 2 gen' rwcur')) (flush_rb br)) by (rewrite !frs_rb_eq, nsome_flush_upd; reflexivity).
cbn [ms_regs ms_mem mkst] in HP2, Hhi2, HJ2, Hr10, Hat2.
set (s' := flush_upd s 2 gen' rwcur') in *.
assert (Hvals' : cgif_vals s' = cgif_vals s) by (subst s'; apply cgif_vals_flush_upd).
assert (Hblk' : cgif_blocks0 g s' N = cgif_blocks0 g s N) by (subst s'; apply cl_flush_upd_blocks0; rewrite Hlen; lia).
assert (HB2' : Permutation (blocks L2 A2) (cgif_blocks0 g s' N ++ rest')) by (rewrite Hblk'; exact HB2).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
destruct (cgif_geom L2 A2 mem2 md2 g s' N rest' HH2 HB2') as ((Hr0' & Hr1' & Hrg') & Hfgeom' & _).
pose proof Hat2 as (Hobj2 & Hraw2 & Hfrs2). rewrite Hvals' in Hobj2.
destruct (obj_cgif_parts mem2 g s Hobj2) as (H15' & Hcur' & _ & Hih' & _).
jafter_call_keep HS 55%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | unfold FLUSH_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq57. cbn [ms_regs mkst] in Hq57. rewrite Hr10 in Hq57. symmetry in Hq57.
add_region HS cl_R2.
2:{ unfold cl_R2, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU8.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE o HH2 Hgin2 ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur']. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih']. }
apply Forall_nil. }
2:{ unfold cl_R2. cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. repeat split; lia. }
add_region HS cl_R1.
2:{ unfold cl_R1. eapply (region_ok_obj_gen ubs0segs _ mem2 8 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[ew_havocA; exact HU8 | lia | lia | exact H15' | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. assert (Hlj : (j < length (vals15 s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
change (length (vals15 s)) with 15%nat in Hlj.
rewrite ew_havoc_old by lia. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj | exact Hlj]. }
2:{ unfold cl_R1, cl_R2. cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU8. repeat split; lia. }
assert (TR2 : forall m', (forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs0segs m' a = mbyte ubs0segs mem2 a) ->
obj_at ubs0segs m' (cg_raw s') LAY_Raw (raw_vals g s') /\ (forall f, In (Some f) (cg_frames s') -> obj_at ubs0segs m' (fr_ptr f) LAY_Frame (frame_vals f))).
{ intros m' Hm'. split.
- eapply obj_at_transport_range; [exact Hraw2 | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply Hm'; lia.
- intros fq Hin. destruct (Hfgeom' fq Hin) as (F0 & F1 & F2). eapply obj_at_transport_range; [exact (Hfrs2 fq Hin) | exact (proj1 LAY_Frame_ok)|]. intros i Hi. apply Hm'; lia. }
assert (HFPin' : forall b n a, In (b, n) (cgif_blocks0 g s' N) -> b <= a < b + n -> inFP FP a) by (rewrite Hblk'; exact HFPin).
jrun LAWS ubs0tbl_ok HS HJ2. { wr_any HU2 HU8 Hgin2 HFPin. }
jbranch ubs0tbl HS; clear Hc.
+
jrun_to LAWS ubs0tbl_ok HS HJ2 CL_CLEAN. { wr_any HU2 HU8 Hgin2 HFPin. }
cgif_obj_low_at 0%nat 1%nat HS HU8 HXn Rg s 59%nat.
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ [?cc; _]) |- _ => rename Hx into Hobj3; set (c := cc) in Hobj3 end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR2 (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia))) as [Hraw3 Hfrs3] end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_clean API IMG FWRITE FCLOSE L A mem md regs0 rg L2 A2 mm md2 g N (set_cur s' c) rest FP (S ++ bytes) (flush_rb br)) end;
[ exact HJ2 | exact Hra0 | exact Htp0 | exact Hal16 | exact Hsp47 | exact HFPin' | exact HFPs | exact HFPlow | | apply set_cur_wf; exact Hwf2 | exact HB2' | | rewrite length_app, Nat2Z.inj_add; unfold FRAME_OUT in *; lia | | | | | | exact HR2 ].
* split; [| split; [exact Hraw3 | exact Hfrs3]]. rewrite cgif_vals_set_cur. unfold vals15. rewrite Hvals'. change (cg_ihead s') with (cg_ihead s). exact Hobj3.
* lazymatch goal with |- sink_at _ ?mm _ _ _ => eapply (sink_at_low L2 A2 mem2 md2 mem2 mm g f (S ++ bytes) md2 HH2 Hgin2 Hfin2); [| exact HSK2] end.
intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia).
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
jrun_to LAWS ubs0tbl_ok HS HJ2 CL_CLEAN. { wr_any HU2 HU8 Hgin2 HFPin. }
cgif_obj_now_at 0%nat 1%nat HS HU8 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj3 end. rewrite <- cgif_vals_split, <- Hvals' in Hobj3.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR2 (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia))) as [Hraw3 Hfrs3] end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (close_clean API IMG FWRITE FCLOSE L A mem md regs0 rg L2 A2 mm md2 g N s' rest FP (S ++ bytes) (flush_rb br)) end;
[ exact HJ2 | exact Hra0 | exact Htp0 | exact Hal16 | exact Hsp47 | exact HFPin' | exact HFPs | exact HFPlow | | exact Hwf2 | exact HB2' | | rewrite length_app, Nat2Z.inj_add; unfold FRAME_OUT in *; lia | | | | | | exact HR2 ].
* split; [exact Hobj3 | split; [exact Hraw3 | exact Hfrs3]].
* lazymatch goal with |- sink_at _ ?mm _ _ _ => eapply (sink_at_low L2 A2 mem2 md2 mem2 mm g f (S ++ bytes) md2 HH2 Hgin2 Hfin2); [| exact HSK2] end.
intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU8; lia).
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
[ YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 88 0 0 (obj_chunks_gen LAY15 32 lits15) ;
YP09.mkRegion (Some 10%nat) 88 96 88 92 [mkChunk 88 (CVal 4 (SOff 47 0)); mkChunk 92 (CVal 4 (SOff 48 0))] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + CLOSE_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(47%nat, mkAF 0 4294967295 0); (48%nat, mkAF 0 4294967295 0);
(49%nat, mkAF (2^64 - 1 - (CEIL_MAX - 96)) (2^64 - 1 - 4096) 0) ] []
[ (SAlu ALU_XOR (SOff 10 0) (SLit (-1)), SOff 49 0) ]).
Ltac cls_words i HS HU2 HE :=
unfold cl_saved_ok; repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned (getr _ ?rr)) =>
let n := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
replace (spv - dd) with (spv + (- dd)) by lia;
eapply (st_chunk_word _ _ _ i _ 2%nat (- dd) (SOff n 0) spv _ HS);
[reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE n rr eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range']
end.
Theorem ubs0_cgif_close_x : close_specX API.
Proof using FCLOSE FLUSHX FWRITE IMG.
intros L A regs mem md g s N rest GPAL gs b HPRE Hid HSLEN Hsp47 G10 Hat Hwf HB00 HREL HRq HROOM.
pose proof HREL as ((Hcurq & Hocc) & HSK & Hlive). set (G := gcfg_of s GPAL) in *.
assert (HB : Permutation (blocks L A) (cgif_blocks0 g s N ++ (cg_file s, FILE_BLOCK) :: rest)) by (eapply Permutation_trans; [exact HB00 | apply cgif_blocks0_perm]).
set (rest' := (cg_file s, FILE_BLOCK) :: rest) in HB.
assert (HN0 : 0 <= N) by (pose proof Hwf as (_ & HW1 & HH1 & HNe & _); rewrite HNe; apply Z.mul_nonneg_nonneg; lia).
assert (HCOv : CLOSE_OUT N = 3 * FRAME_OUT N + 1) by reflexivity. unfold FRAME_OUT in HCOv.
pose proof HPRE as (HH & Hra0 & Hst & Htp0 & Herr).
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof Hwf as (Hlen & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HCSv : CLOSE_STK = 9728) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
assert (Hspm : (sp0 - 48) mod 16 = 0) by (replace (sp0 - 48) with (sp0 + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (FP := cgif_fp g s N).
assert (HFPin : forall b' n a, In (b', n) (cgif_blocks0 g s N) -> b' <= a < b' + n -> inFP FP a).
{ intros b' n a Hbn Ha. subst FP. unfold cgif_fp. apply (proj2 (inFP_cons _ _ _ _)). right. apply (proj2 (inFP_blocks_fp _ _)). exists b', n. split; [apply cgif_blocks0_in; exact Hbn | exact Ha]. }
assert (HFPs : forall a, inFP (sink_fp (cg_file s)) a -> inFP FP a).
{ intros a Ha. subst FP. unfold cgif_fp. unfold sink_fp in Ha. apply inFP_cons in Ha. apply (proj2 (inFP_cons _ _ _ _)). destruct Ha as [Ha|Ha]; [left; exact Ha | right].
apply inFP_cons in Ha. destruct Ha as [Ha|Ha]; [| exfalso; exact (YI04.inFP_nil _ Ha)].
apply (proj2 (inFP_blocks_fp _ _)). exists (cg_file s), FILE_BLOCK. split; [unfold cgif_blocks; right; right; left; reflexivity | cbn [fst snd] in Ha; lia]. }
assert (HFPc : forall a, inFP (cgif_fp g s N) a -> inFP FP a) by (intros a Ha; exact Ha).
assert (HFPlow : forall a, inFP FP a -> a < alloc_ceiling).
{ intros a Ha. subst FP. unfold cgif_fp in Ha. apply inFP_cons in Ha. destruct Ha as [Ha|Ha]; [unfold sink_token in Ha; cbn [fst snd] in Ha; pose proof (proj1 alloc_ceiling_val); lia|].
apply inFP_blocks_fp in Ha as (b' & n & Hbn & Hba).
destruct (blocks_range _ _ LAWS L A mem md b' n HH ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB00|]; apply in_app_iff; left; exact Hbn)). lia. }
assert (Hfin : In (cg_file s, FILE_BLOCK) (blocks L A)) by (eapply Permutation_in; [apply Permutation_sym; exact HB|]; apply in_app_iff; right; left; reflexivity).
assert (Rrw : 0 <= rw_cur s < 2 ^ 32) by (pose proof (obj_at_range _ _ _ _ _ (proj1 (proj2 Hat)) 8%nat (rw_cur s) eq_refl) as X; exact X).
assert (Hgin : In (g, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (cgif_geom L A mem md g s N rest' HH HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
set (E := Ereg regs (map (Z_to_bv 64) (cgif_vals s) ++ map (Z_to_bv 64) [2 ^ 64 - 1 - g] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error (cgif_vals s) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HXn : forall n j v, n = (32 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) by (intros n j v -> Hj; apply HX; exact Hj).
assert (HY49 : ew E 49 = Z_to_bv 64 (2 ^ 64 - 1 - g)) by (subst E; replace 49%nat with (32 + (length (cgif_vals s) + 0))%nat by reflexivity; apply Ereg_vals2; reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = g) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
destruct (obj_cgif_parts mem g s Hobj) as (H15 & Hcur & Rcur & Hih & Rih).
assert (HS : st_ok ubs0segs E ss_close0 (mkst regs (Z_to_bv 64 CLOSE) mem (seg_rom ubs0segs))).
{ unfold ss_close0. replace ubs0_A_cgif_close with CLOSE by reflexivity. apply entry_st_ok_any.
- subst E. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack ubs0segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ eapply (region_ok_obj_gen ubs0segs _ mem 10 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[exact HU10 | lia | lia | exact H15 | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj|].
apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L A mem md g CGIF_SIZE o HH Hgin ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU10. repeat split; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [| split; [exact I | split; [| exact I]]].
{ unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Rg 15%nat _ eq_refl) as R47. pose proof (Rg 16%nat _ eq_refl) as R48.
cbn [nth snd LAY_CGIF Z.of_N] in R47, R48.
rewrite HU2, HU10, (HXn 47%nat 15%nat _ eq_refl eq_refl), (HXn 48%nat 16%nat _ eq_refl eq_refl), HY49.
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
apply (UIZp.clz_not_alias E 10 49 g); [rewrite (HE 10%nat 10%bv eq_refl); exact G10 | lia | exact HY49]. }
pose proof (journal_init ubs0_msyms MR CLOSE_STK FP L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 CLOSE) mem (seg_rom ubs0segs))) in HJ. fold sp0 in HJ.
assert (TR : forall m', (forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs0segs m' a = mbyte ubs0segs mem a) ->
obj_at ubs0segs m' (cg_raw s) LAY_Raw (raw_vals g s) /\ (forall f, In (Some f) (cg_frames s) -> obj_at ubs0segs m' (fr_ptr f) LAY_Frame (frame_vals f))).
{ intros m' Hm'. split.
- eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply Hm'; lia.
- intros fq Hin. destruct (Hfgeom fq Hin) as (F0 & F1 & F2). eapply obj_at_transport_range; [exact (Hfrs fq Hin) | exact (proj1 LAY_Frame_ok)|]. intros i Hi. apply Hm'; lia. }
jrun LAWS ubs0tbl_ok HS HJ. { wr_any HU2 HU10 Hgin HFPin. }
jbranch ubs0tbl HS.
-
assert (Hcur0 : cg_cur s <> 0).
{ intros E0. rewrite branch_ne_U, U_lit, U_SExt, (U_atom _ 47 (cg_cur s)) in Hc; [| ew_havocA; apply (HXn 47%nat 15%nat _ eq_refl eq_refl) | lia | lia]. rewrite E0 in Hc. cbv in Hc. discriminate Hc. }
clear Hc.
assert (Hdead : YO07.s_cur gs <> YO07.C_OK) by (rewrite <- Hcurq; unfold YO07.C_OK; intros E0; apply Hcur0; apply (proj1 (rc_int_zero _ Rcur)); exact E0).
jrun_to LAWS ubs0tbl_ok HS HJ CL_CLEAN. { wr_any HU2 HU10 Hgin HFPin. }
cgif_obj_now_p 10%nat 1%nat 2%nat HS HU10 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw2 Hfrs2] end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SR_mono; [eapply (close_clean API IMG FWRITE FCLOSE L A mem md regs rg L A mm md g N s rest FP (concat (YO07.s_out gs)) b) |] end;
[ exact HJ | exact Hra0 | exact Htp0 | exact Hal16 | exact Hsp47 | exact HFPin | exact HFPs | exact HFPlow | | exact Hwf | exact HB | | lia | | | | | | exact HRq | ].
+ split; [exact Hobj2 | split; [exact Hraw2 | exact Hfrs2]].
+ lazymatch goal with |- sink_at _ ?mm _ _ _ => eapply (sink_at_low L A mem md mem mm g (cg_file s) _ md HH Hgin Hfin); [| exact HSK] end.
intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia).
+ cls_words 0%nat HS HU2 HE.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact HY49).
+ unfold cl_untouched; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+
cbv beta. intros c' Hc'. rewrite (close_gif_dead G gs Hdead).
eapply (close_postX_out regs FP L A mem md rest _ _ b N (qcount gs) c' Hc').
pose proof Hwf as (Hlen3 & _). destruct (cg_frames s) as [|o0 [|o1 [|o2 [|]]]] eqn:Hfs; try (cbn in Hlen3; discriminate Hlen3).
eapply (frs_rb_close N [o0; o1; o2] b b 0 (qcount gs) HN0); [unfold CLOSE_K, FLUSH_K, RAWADD_K, LZW_K; lia | unfold rb_le, rb_acc; cbn; lia | symmetry; exact (qcount_nsome s gs o0 o1 o2 Hfs Hocc)].
-
assert (Hcur0 : cg_cur s = 0).
{ rewrite branch_ne_U, U_lit, U_SExt, (U_atom _ 47 (cg_cur s)) in Hc; [| ew_havocA; apply (HXn 47%nat 15%nat _ eq_refl eq_refl) | lia | lia].
apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc. change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc.
pose proof (sext32_low (cg_cur s) Rcur) as X. rewrite Hc in X. change (0 mod 2 ^ 32) with 0 in X. lia. }
clear Hc.
assert (HcurOK : YO07.s_cur gs = YO07.C_OK) by (rewrite <- Hcurq, Hcur0; reflexivity).
destruct (Hlive (or_introl HcurOK)) as (Hrc & Hrat & Hihd & Hgp & Hq0 & Hq1 & Hq2).
pose proof (close_gif_ok G gs HcurOK) as HCG.
jrun LAWS ubs0tbl_ok HS HJ. { wr_any HU2 HU10 Hgin HFPin. }
jbranch ubs0tbl HS.
+
rewrite branch_eq_U, (U_atom _ 33 (frame_ptr (nth 1 (cg_frames s) None))), U_lit in Hc;
[| lia | ew_havocA; apply (HXn 33%nat 1%nat _ eq_refl eq_refl) | ].
2:{ pose proof (Rg 1%nat _ eq_refl) as R33. cbn [nth snd LAY_CGIF Z.of_N] in R33. lia. }
destruct (nth 1 (cg_frames s) None) as [f1|] eqn:Hn1.
{ exfalso. destruct (Hfgeom f1 ltac:(rewrite <- Hn1; apply nth_In; rewrite Hlen; lia)) as (F0 & _). cbn [frame_ptr] in Hc. destruct (Z.eqb_spec (fr_ptr f1) 0); [lia | discriminate Hc]. }
clear Hc. assert (Hq1n : YO07.s_q1 gs = None) by (destruct (YO07.s_q1 gs); [exact (False_ind _ Hq1) | reflexivity]).
jrun_to LAWS ubs0tbl_ok HS HJ CL_LOOP. { wr_any HU2 HU10 Hgin HFPin. }
cgif_obj_now_p 10%nat 1%nat 2%nat HS HU10 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj2 end. rewrite <- cgif_vals_split in Hobj2.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw2 Hfrs2] end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SR_mono; [eapply (close_iter2 L A mem md regs rg L A mm md g N s rest FP (concat (YO07.s_out gs)) GPAL (YO07.s_q1 gs) (YO07.s_q2 gs) b) |] end;
[ exact HJ | exact Hid | exact Hra0 | exact Htp0 | exact Hal16 | exact Hsp47 | exact HFPin | exact HFPs | exact HFPc | exact HFPlow | | exact Hwf | exact HB | | unfold FRAME_OUT in *; lia | | exact Hrat | exact Rrw | exact HRq | apply close_room_flush1; [exact HN0 | exact HROOM] | | | | | | | | | ].
* split; [exact Hobj2 | split; [exact Hraw2 | exact Hfrs2]].
* lazymatch goal with |- sink_at _ ?mm _ _ _ => eapply (sink_at_low L A mem md mem mm g (cg_file s) _ md HH Hgin Hfin); [| exact HSK] end.
intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia).
* lazymatch goal with |- cl_vals ?mm _ _ _ _ _ => eapply (cl_vals_low L A mem md mem mm g s N rest' GPAL _ _ HH HB) end.
{ intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia). }
split; [exact Hgp | split; [rewrite Hn1; eapply oframe_relb_weaken; exact Hq1 | exact Hq2]].
* cls_words 0%nat HS HU2 HE.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite HU10; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact HY49).
* reg_nowF HS ltac:(rewrite HU10; reflexivity).
* reg_nowF HS ltac:(reflexivity).
* reg_nowF HS ltac:(reflexivity).
* unfold cl_untouched; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
*
cbv beta. intros c' Hc'. rewrite HCG. unfold cl_bytes, cl_code, cl_rcur1 in Hc' |- *. rewrite Hq1n in Hc' |- *. rewrite Z.eqb_refl. rewrite Hrc in Hc'. cbn [app] in Hc' |- *.
rewrite <- app_assoc. eapply (close_postX_out regs FP L A mem md rest _ _ b N (qcount gs) c' Hc').
pose proof Hwf as (Hlen3 & _). destruct (cg_frames s) as [|o0 [|o1 [|o2 [|]]]] eqn:Hfs; try (cbn in Hlen3; discriminate Hlen3). cbn [nth].
destruct o2 as [f2|]; cbn [cl_brb].
{ rewrite flush_rb_acc. eapply (frs_rb_close N _ b _ FLUSH_K (qcount gs) HN0); [unfold CLOSE_K, FLUSH_K, RAWADD_K, LZW_K; lia | apply rb_le_refl | symmetry; exact (qcount_nsome s gs o0 o1 (Some f2) Hfs Hocc)]. }
{ eapply (frs_rb_close N _ b b 0 (qcount gs) HN0); [unfold CLOSE_K, FLUSH_K, RAWADD_K, LZW_K; lia | unfold rb_le, rb_acc; cbn; lia | symmetry; exact (qcount_nsome s gs o0 o1 None Hfs Hocc)]. }
+
rewrite branch_eq_U, (U_atom _ 33 (frame_ptr (nth 1 (cg_frames s) None))), U_lit in Hc;
[| lia | ew_havocA; apply (HXn 33%nat 1%nat _ eq_refl eq_refl) | ].
2:{ pose proof (Rg 1%nat _ eq_refl) as R33. cbn [nth snd LAY_CGIF Z.of_N] in R33. lia. }
destruct (nth 1 (cg_frames s) None) as [f1|] eqn:Hn1; [| cbn in Hc; discriminate Hc]. clear Hc.
destruct (YO07.s_q1 gs) as [cur1|] eqn:Hq1e; [| exact (False_ind _ Hq1)]. cbn [oframe_relb] in Hq1.
assert (Ho1 : nth_error (cg_frames s) 1 = Some (Some f1)) by (rewrite (nth_error_nth' _ None) by lia; rewrite Hn1; reflexivity).
assert (Hf1in : In (Some f1) (cg_frames s)) by (eapply nth_error_In; exact Ho1).
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_flushFrame. { wr_any HU2 HU10 Hgin HFPin. }
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
pose proof (vblocks_TR L A mem md mem (ms_mem msx) g s N rest' HH HB ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as KV1;
pose proof (sink_at_low L A mem md mem (ms_mem msx) g (cg_file s) _ md HH Hgin Hfin ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia)) HSK) as HSK1 end.
pose proof (gpal_keptV _ _ s N GPAL KV1 Hgp) as Hgp1.
pose proof (oframe_relb_keptV _ _ s N false 0 _ KV1 Hq0) as Hq01.
pose proof (oframe_relb_keptV _ _ s N true 1 (Some cur1) KV1 ltac:(rewrite Hn1; exact Hq1)) as Hq11. rewrite Hn1 in Hq11. cbn [oframe_relb] in Hq11.
pose proof (oframe_relb_keptV _ _ s N true 2 _ KV1 Hq2) as Hq21.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2 (r gen' rwcur' code : Z) (bytes : list Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 (ubs0_A_cgif_close + 0x5c)) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR CLOSE_STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs msx) regs2 /\ st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 1 gen' rwcur') /\ cgif_wf (flush_upd s 1 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks0 g s N ++ rest') /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 48 - FLUSH_STK <= x < sp0 - 48) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem msx) x /\ (writable_at ubs0segs (ms_mem msx) x <-> writable_at ubs0segs mem2 x)) /\
YO07.flush_frame G (rc_int (rw_cur s)) cur1 (YO07.s_q0 gs) = (code, bytes) /\ Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem2 md2 (cg_file s) (concat (YO07.s_out gs) ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N /\ res_ok A2 (flush_rb b) /\
cl_vals mem2 (flush_upd s 1 gen' rwcur') N GPAL (Some cur1) (YO07.s_q2 gs))
end.
{ eapply SR_mono.
{ eapply (jcall ubs0_msyms MR) with (STK1 := FLUSH_STK) (FP1 := cgif_fp g s N)
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => exists (r gen' rwcur' code : Z) (bytes : list Z),
st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem2 g (flush_upd s 1 gen' rwcur') /\ cgif_wf (flush_upd s 1 gen' rwcur') N /\
Permutation (blocks L2 A2) (cgif_blocks0 g s N ++ rest') /\
YO07.flush_frame G (rc_int (rw_cur s)) cur1 (YO07.s_q0 gs) = (code, bytes) /\ Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem2 md2 (cg_file s) (concat (YO07.s_out gs) ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N /\ res_ok A2 (flush_rb b) /\
cl_vals mem2 (flush_upd s 1 gen' rwcur') N GPAL (Some cur1) (YO07.s_q2 gs));
[ exact HS | reflexivity | exact HJ | exact Hm1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | unfold FLUSH_STK; lia | rewrite Hsp; unfold FLUSH_STK; lia | rewrite Hsp; lia | exact Hm4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (FLUSHX L A _ _ md g s N 1%nat f1 rest (concat (YO07.s_out gs)) GPAL cur1 (YO07.s_q0 gs) b HPRE1 Hid);
[ exact HSK1 | unfold FRAME_OUT in *; lia | rewrite Hsp; lia | | | exact Hwf | left; reflexivity | exact Ho1 | | | exact HB00 | exact Hgp1 | exact Hq11 | exact Hq01 | exact Hrat | exact HRq | apply close_room_flush1; [exact HN0 | exact HROOM] ].
+ rewrite Hm10. ew_havocA. rewrite <- HU10. symmetry. apply Z_to_bv_bv_unsigned.
+ split; [exact Hobj1 | split; [exact Hraw1 | exact Hfrs1]].
+ rewrite Hm11. ew_havocA. rewrite (HXn 33%nat 1%nat _ eq_refl eq_refl), Hn1. reflexivity.
+ rewrite Hm12. ew_havocA. rewrite (HXn 32%nat 0%nat _ eq_refl eq_refl). reflexivity. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & rwcur' & -> & HJc & HP & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & (code & bytes & Hff & Hrc2 & Hrw & HSK2 & Hlenb) & HR2 & Hkeepv).
exists L2, A2, regs2, mem2, md2. split; [rewrite Hm1; reflexivity|]. split; [exact HJc|]. split; [exact HP|].
exists r, (fl_gen3 G cur1 (YO07.s_q0 gs)), rwcur', code, bytes. repeat (split; [assumption|]).
split; [eapply Permutation_trans; [exact HB2 | apply cgif_blocks0_perm]|].
repeat (split; [assumption|]).
lazymatch type of HPRE1 with fn_pre _ _ _ _ _ _ ?mm _ =>
eapply (cl_vals_flush1 L A mem md mm mem2 g s N rest GPAL f1 cur1 (YO07.s_q2 gs) _ rwcur' HH HB Hlen Hn1 Hgp1 Hq11 Hq21 Hkeepv) end.
- intros a Ha. split; [exact (HFPc a Ha) | apply HFPlow; exact (HFPc a Ha)]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & code & bytes & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hff & Hrc2 & Hrw & HSK2 & Hlenb & HR2 & HV2)).
exists L2, A2, regs2, mem2, md2, r, gen', rwcur', code, bytes. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
repeat (split; [assumption|]). split; [| repeat (split; [assumption|]); exact HV2].
pose proof HJc2 as (_ & _ & Hhi2 & _). rewrite Hsp in Hhi2. exact Hhi2. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & r & gen' & rwcur' & code & bytes & -> & HJ2 & HP2 & Hid2 & Hr10 & Hr & Hat2 & Hwf2 & HB2 & Hhi2 & Hff & Hrc2 & Hrw & HSK2 & Hlenb & HR2 & HV2). clear HJ.
assert (Hcode : - 2 ^ 31 <= code < 2 ^ 31).
{ pose proof (rc_int_range (rw_cur s) Rrw). destruct (flush_frame_code G _ _ _ _ _ Hff) as [Ec|[Ec|[Ec|Ec]]]; rewrite Ec; unfold YO07.R_ERROR, YO07.R_EINDEX, YO07.R_OK; lia. }
assert (Hfin2 : In (cg_file s, FILE_BLOCK) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2|]; apply in_app_iff; right; left; reflexivity).
cbn [ms_regs ms_mem mkst] in HP2, Hhi2, HJ2, Hr10, Hat2.
set (s' := flush_upd s 1 gen' rwcur') in *.
assert (Hvals' : cgif_vals s' = cgif_vals s) by (subst s'; apply cgif_vals_flush_upd).
assert (Hblk' : cgif_blocks0 g s' N = cgif_blocks0 g s N) by (subst s'; apply cl_flush_upd_blocks0; rewrite Hlen; lia).
assert (HB2' : Permutation (blocks L2 A2) (cgif_blocks0 g s' N ++ rest')) by (rewrite Hblk'; exact HB2).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
destruct (cgif_geom L2 A2 mem2 md2 g s' N rest' HH2 HB2') as ((Hr0' & Hr1' & Hrg') & Hfgeom' & _).
pose proof Hat2 as (Hobj2 & Hraw2 & Hfrs2). rewrite Hvals' in Hobj2.
destruct (obj_cgif_parts mem2 g s Hobj2) as (H15' & Hcur' & _ & Hih' & _).
jafter_call_keep HS 53%nat regs2 mem2 HP2 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | unfold FLUSH_STK; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq57. cbn [ms_regs mkst] in Hq57. rewrite Hr10 in Hq57. symmetry in Hq57.
add_region HS (YP09.mkRegion (Some 10%nat) 88 96 88 92 [mkChunk 88 (CVal 4 (SOff 47 0)); mkChunk 92 (CVal 4 (SOff 48 0))]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 g CGIF_SIZE o HH2 Hgin2 ltac:(lia))). }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_cur s)); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat (cg_cur s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hcur']. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_ihead s)); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 48%nat 16%nat (cg_ihead s) eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hih']. }
apply Forall_nil. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU10. repeat split; lia. }
add_region HS (YP09.mkRegion (Some 10%nat) 0 88 0 0 (obj_chunks_gen LAY15 32 lits15)).
2:{ eapply (region_ok_obj_gen ubs0segs _ mem2 10 g 88 0 0 LAY15 (vals15 s) 32 lits15);
[ew_havocA; exact HU10 | lia | lia | exact H15' | reflexivity | | apply lits15_ok | intros i Hi; lia].
intros j v Hj. assert (Hlj : (j < length (vals15 s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
change (length (vals15 s)) with 15%nat in Hlj.
rewrite ew_havoc_old by lia. apply HX. rewrite cgif_vals_split. rewrite nth_error_app1; [exact Hj | exact Hlj]. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU10. repeat split; lia. }
assert (TR2 : forall m', (forall a, 4096 <= a < alloc_ceiling -> (g + CGIF_SIZE <= a \/ a + 1 <= g + 88) -> mbyte ubs0segs m' a = mbyte ubs0segs mem2 a) ->
obj_at ubs0segs m' (cg_raw s') LAY_Raw (raw_vals g s') /\ (forall f, In (Some f) (cg_frames s') -> obj_at ubs0segs m' (fr_ptr f) LAY_Frame (frame_vals f))).
{ intros m' Hm'. split.
- eapply obj_at_transport_range; [exact Hraw2 | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply Hm'; lia.
- intros fq Hin. destruct (Hfgeom' fq Hin) as (F0 & F1 & F2). eapply obj_at_transport_range; [exact (Hfrs2 fq Hin) | exact (proj1 LAY_Frame_ok)|]. intros i Hi. apply Hm'; lia. }
assert (HFPin' : forall b n a, In (b, n) (cgif_blocks0 g s' N) -> b <= a < b + n -> inFP FP a) by (rewrite Hblk'; exact HFPin).
jrun LAWS ubs0tbl_ok HS HJ2. { wr_any HU2 HU10 Hgin2 HFPin. }
jbranch ubs0tbl HS.
*
assert (Hrz : r <> 0).
{ intros E0. rewrite branch_ne_U, U_lit, (U_atom _ 57 r) in Hc; [| exact Hq57 | lia | lia]. rewrite E0 in Hc. cbv in Hc. discriminate Hc. }
clear Hc.
assert (Hcnz : code <> 0) by (intros E0; apply Hrz; apply (proj2 (code_zero_iff r code Hr ltac:(lia) Hrc2)); exact E0).
pose proof (flush_frame_fail_nil G _ _ _ _ _ Hff Hcnz) as Hbn.
jrun_to LAWS ubs0tbl_ok HS HJ2 CL_CLEAN. { wr_any HU2 HU10 Hgin2 HFPin. }
cgif_obj_low_p 10%nat 0%nat 1%nat HS HU10 HXn Rg s 57%nat.
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ [?cc; _]) |- _ => rename Hx into Hobj3; set (c := cc) in Hobj3 end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR2 (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw3 Hfrs3] end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SR_mono; [eapply (close_clean API IMG FWRITE FCLOSE L A mem md regs rg L2 A2 mm md2 g N (set_cur s' c) rest FP (concat (YO07.s_out gs) ++ bytes) (flush_rb b)) |] end;
[ exact HJ2 | exact Hra0 | exact Htp0 | exact Hal16 | exact Hsp47 | exact HFPin' | exact HFPs | exact HFPlow | | apply set_cur_wf; exact Hwf2 | exact HB2' | | rewrite length_app, Nat2Z.inj_add; unfold FRAME_OUT in *; lia | | | | | | exact HR2 | ].
-- split; [| split; [exact Hraw3 | exact Hfrs3]]. rewrite cgif_vals_set_cur. unfold vals15. rewrite Hvals'. change (cg_ihead s') with (cg_ihead s). exact Hobj3.
-- lazymatch goal with |- sink_at _ ?mm _ _ _ => eapply (sink_at_low L2 A2 mem2 md2 mem2 mm g (cg_file s) _ md2 HH2 Hgin2 Hfin2); [| exact HSK2] end.
intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia).
-- cls_words 2%nat HS HU2 HE.
-- reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
-- reg_nowF HS ltac:(rewrite HU10; reflexivity).
-- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact HY49).
-- unfold cl_untouched; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
--
cbv beta. intros c' Hc'. rewrite HCG. unfold cl_bytes, cl_code, cl_rcur1 in Hc' |- *. rewrite <- Hrc. rewrite Hff. cbn [fst snd].
unfold YO07.C_OK. destruct (Z.eqb_spec code 0) as [E0|_]; [exfalso; exact (Hcnz E0)|].
rewrite Hbn in Hc' |- *. cbn [app] in Hc' |- *. rewrite !app_nil_r in Hc' |- *.
eapply (close_postX_out regs FP L A mem md rest _ _ b N (qcount gs) c' Hc').
rewrite flush_rb_acc. eapply (frs_rb_close N _ b _ FLUSH_K (qcount gs) HN0); [unfold CLOSE_K, FLUSH_K, RAWADD_K, LZW_K; lia | apply rb_le_refl |].
change (cg_frames (set_cur s' c)) with (cg_frames s'). subst s'. rewrite nsome_flush_upd.
pose proof Hwf as (Hlen3 & _). destruct (cg_frames s) as [|o0 [|o1 [|o2 [|]]]] eqn:Hfs; try (cbn in Hlen3; discriminate Hlen3).
symmetry. exact (qcount_nsome s gs o0 o1 o2 Hfs Hocc).
*
assert (Hrz : r = 0).
{ rewrite branch_ne_U, U_lit, (U_atom _ 57 r) in Hc; [| exact Hq57 | lia | lia]. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc. exact Hc. }
clear Hc. assert (Hcz : code = 0) by (apply (proj1 (code_zero_iff r code Hr ltac:(lia) Hrc2)); exact Hrz).
jrun_to LAWS ubs0tbl_ok HS HJ2 CL_LOOP. { wr_any HU2 HU10 Hgin2 HFPin. }
cgif_obj_now_p 10%nat 0%nat 1%nat HS HU10 HXn Rg s (cg_cur s) (SOff 47 0) ltac:(cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HXn 47%nat 15%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity).
match goal with Hx : obj_at _ _ g LAY_CGIF (vals15 s ++ _) |- _ => rename Hx into Hobj3 end. rewrite <- cgif_vals_split, <- Hvals' in Hobj3.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
destruct (TR2 (ms_mem msx) ltac:(intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia))) as [Hraw3 Hfrs3] end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SR_mono; [eapply (close_iter2 L A mem md regs rg L2 A2 mm md2 g N s' rest FP (concat (YO07.s_out gs) ++ bytes) GPAL (Some cur1) (YO07.s_q2 gs) (flush_rb b)) |] end;
[ exact HJ2 | exact Hid2 | exact Hra0 | exact Htp0 | exact Hal16 | exact Hsp47 | exact HFPin' | exact HFPs | subst s'; unfold cgif_fp; rewrite flush_upd_blocks by (rewrite Hlen; lia); exact HFPc | exact HFPlow | | exact Hwf2 | exact HB2' | | rewrite length_app, Nat2Z.inj_add; unfold FRAME_OUT in *; lia | | exact Hrat | subst s'; cbn [rw_cur flush_upd]; rewrite Hrw; apply Z.mod_pos_bound; lia | exact HR2 | apply close_room_flush2; exact HROOM | | | | | | | | | ].
-- split; [exact Hobj3 | split; [exact Hraw3 | exact Hfrs3]].
-- lazymatch goal with |- sink_at _ ?mm _ _ _ => eapply (sink_at_low L2 A2 mem2 md2 mem2 mm g (cg_file s) _ md2 HH2 Hgin2 Hfin2); [| exact HSK2] end.
intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia).
-- lazymatch goal with |- cl_vals ?mm _ _ _ _ _ => eapply (cl_vals_low L2 A2 mem2 md2 mem2 mm g s' N rest' GPAL _ _ HH2 HB2'); [| exact HV2] end.
intros a Ha1 Ha2; cbn [ms_mem mkst] in *; hist ltac:(rewrite ?HU2, ?HU10; lia).
-- cls_words 2%nat HS HU2 HE.
-- reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
-- reg_nowF HS ltac:(rewrite HU10; reflexivity).
-- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact HY49).
-- reg_nowF HS ltac:(rewrite HU10; reflexivity).
-- reg_nowF HS ltac:(reflexivity).
-- reg_nowF HS ltac:(reflexivity).
-- unfold cl_untouched; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
--
cbv beta. intros c' Hc'. rewrite HCG. unfold cl_bytes, cl_code, cl_rcur1 in Hc' |- *. rewrite Hq1e. rewrite <- Hrc. rewrite !Hff. cbn [fst snd].
rewrite Hcz. cbn [Z.eqb YO07.C_OK].
replace (rc_int (rw_cur s')) with 0 in Hc' by (subst s'; cbn [rw_cur flush_upd]; rewrite Hrw, Hcz; reflexivity).
repeat rewrite <- app_assoc in Hc'. repeat rewrite <- app_assoc. eapply (close_postX_out regs FP L A mem md rest _ _ b N (qcount gs) c' Hc').
pose proof Hwf as (Hlen3 & _). subst s'. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|]]]] eqn:Hfs; try (cbn in Hlen3; discriminate Hlen3).
cbn [nth] in Hn1. subst o1. rewrite (flush_upd1_frames s _ _ o0 f1 o2 Hfs). cbn [nth].
destruct o2 as [f2|]; cbn [cl_brb].
{ rewrite flush_rb_acc2. eapply (frs_rb_close N _ b _ CLOSE_K (qcount gs) HN0); [unfold CLOSE_K, FLUSH_K, RAWADD_K, LZW_K; lia | apply rb_le_refl | symmetry; exact (qcount_nsome s gs o0 (Some f1) (Some f2) Hfs Hocc)]. }
{ rewrite flush_rb_acc. eapply (frs_rb_close N _ b _ FLUSH_K (qcount gs) HN0); [unfold CLOSE_K, FLUSH_K, RAWADD_K, LZW_K; lia | apply rb_le_refl | symmetry; exact (qcount_nsome s gs o0 (Some f1) None Hfs Hocc)]. }
Qed.
Theorem ubs0_close_specX : close_specX API.
Proof using FCLOSE FLUSHX FWRITE IMG. exact ubs0_cgif_close_x. Qed.
End S.
End h.
