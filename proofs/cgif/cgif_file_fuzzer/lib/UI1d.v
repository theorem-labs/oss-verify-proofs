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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w UI4l UI21 UI2m UI5l YI6b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition AF : Z := ubs0_A_cgif_addframe.
Definition AF_RETC : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0xc4).
Definition AF_RET  : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0xc8).
Definition AF_B    : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0xf4).
Definition AF_LOOP : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x17c).
Definition AF_C    : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x278).
Definition AF_D    : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x308).
Definition AF_E    : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x3bc).
Definition AF_SAME : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x218).
Definition AF_FAIL : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x4bc).
Definition AF_FRAME : Z := 64.
Definition set_frames (s : cgif_st) (fr : list (option frame_st)) : cgif_st :=
mkCgif fr (cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) (cg_cur s) (cg_ihead s)
(rw_gct s) (rw_attr s) (rw_loops s) (rw_cur s) (cg_file s).
Definition set_ihead (s : cgif_st) (ih : Z) : cgif_st :=
mkCgif (cg_frames s) (cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) (cg_cur s) ih
(rw_gct s) (rw_attr s) (rw_loops s) (rw_cur s) (cg_file s).
Definition set_fr_delay (f : frame_st) (v : Z) : frame_st :=
mkFrame (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) (fr_gen f) v (fr_nlp f) (fr_ctidx f) (fr_disp f) (fr_tidx f).
Definition set_fr_tidx (f : frame_st) (v : Z) : frame_st :=
mkFrame (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) (fr_gen f) (fr_delay f) (fr_nlp f) (fr_ctidx f) (fr_disp f) v.
Lemma cgif_vals_set_cur_ls : forall s c, cgif_vals (set_cur s c) = list_set (cgif_vals s) 15 c.
Proof using. intros. reflexivity. Qed.
Lemma cgif_vals_set_ihead_ls : forall s ih, cgif_vals (set_ihead s ih) = list_set (cgif_vals s) 16 ih.
Proof using. intros. reflexivity. Qed.
Definition set_fr_gen_disp (f : frame_st) (gen disp : Z) : frame_st :=
mkFrame (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) gen (fr_delay f) (fr_nlp f) (fr_ctidx f) disp (fr_tidx f).
Definition same_geom (s s0 : cgif_st) : Prop :=
cg_W s = cg_W s0 /\ cg_H s = cg_H s0 /\ cg_attr s = cg_attr s0 /\ cg_raw s = cg_raw s0 /\
cg_pal s = cg_pal s0 /\ cg_ngp s = cg_ngp s0.
Lemma same_geom_refl : forall s, same_geom s s.
Proof using. intros s. repeat split; reflexivity. Qed.
Lemma cgif_vals_set_frames : forall s fr,
cgif_vals (set_frames s fr) = frame_ptr (nth 0 fr None) :: frame_ptr (nth 1 fr None) :: frame_ptr (nth 2 fr None) :: skipn 3 (cgif_vals s).
Proof using. intros. reflexivity. Qed.
Lemma cgif_blocks_set_frames : forall g s fr N,
cgif_blocks g (set_frames s fr) N = (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) :: pal_blocks s ++ frames_blocks N fr.
Proof using. intros. reflexivity. Qed.
Lemma pal_blocks_set_frames : forall s fr, pal_blocks (set_frames s fr) = pal_blocks s.
Proof using. intros. reflexivity. Qed.
Lemma frame_blocks_set_fr_delay : forall N f v, frame_blocks N (set_fr_delay f v) = frame_blocks N f.
Proof using. intros. reflexivity. Qed.
Lemma frame_blocks_set_fr_gen_disp : forall N f a b, frame_blocks N (set_fr_gen_disp f a b) = frame_blocks N f.
Proof using. intros. reflexivity. Qed.
Lemma frame_blocks_set_fr_gen : forall N f a, frame_blocks N (set_fr_gen f a) = frame_blocks N f.
Proof using. intros. reflexivity. Qed.
Lemma frames_blocks_app : forall N l1 l2, frames_blocks N (l1 ++ l2) = frames_blocks N l1 ++ frames_blocks N l2.
Proof using. intros N l1 l2. unfold frames_blocks. rewrite flat_map_app. reflexivity. Qed.
Lemma frames_blocks_3 : forall N o0 o1 o2,
frames_blocks N [o0; o1; o2] = frames_blocks N [o0] ++ frames_blocks N [o1] ++ frames_blocks N [o2].
Proof using. intros. unfold frames_blocks. cbn. rewrite !app_nil_r. reflexivity. Qed.
Lemma frames_blocks_some : forall N f, frames_blocks N [Some f] = frame_blocks N f.
Proof using. intros. unfold frames_blocks. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma frames_blocks_none : forall N, frames_blocks N [None] = [].
Proof using. intros. reflexivity. Qed.
Lemma frames3 : forall s N, cgif_wf s N -> exists o0 o1 o2, cg_frames s = [o0; o1; o2].
Proof using.
intros s N (Hlen & _). destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate.
exists o0, o1, o2. reflexivity.
Qed.
Lemma cgif_wf_intro : forall s fr cur ih N,
cgif_wf s N -> length fr = 3%nat ->
(ih = 1 \/ (ih = 2 /\ nth 1 fr None <> None)) ->
(forall f, In (Some f) fr -> frame_wf (cg_attr s) f) ->
cgif_wf (mkCgif fr (cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) cur ih
(rw_gct s) (rw_attr s) (rw_loops s) (rw_cur s) (cg_file s)) N.
Proof using.
intros s fr cur ih N (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf) Hl Hi Hf.
unfold cgif_wf. cbn. repeat (split; [assumption|]). exact Hf.
Qed.
Section q.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition af_post (regs0 : bvmap 5 word) (g N : Z) (s0 : cgif_st) (CB rest FP : list (Z * Z)) L A mem md (c' : config) : Prop :=
exists L' A' regs' mem' md' (s' : cgif_st),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR ADDFRAME_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
cgif_at mem' g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s0 /\ cg_H s' = cg_H s0 /\ cg_attr s' = cg_attr s0 /\ cg_raw s' = cg_raw s0 /\
Permutation (blocks L' A') (cgif_blocks g s' N ++ CB ++ rest).
End q.
Definition AF_SAVED : list reg := [1; 8; 9; 18; 19; 20; 21; 22]%bv.
Definition AF_ATOMS : list reg := (AF_SAVED ++ [23; 24; 25; 26])%bv.
Definition af_saved_vals (regs0 : bvmap 5 word) : list Z := map (fun r : reg => bv_unsigned (getr regs0 r)) AF_ATOMS.
Definition af_saved_ok (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j (r : reg), nth_error AF_SAVED j = Some r -> word_mem ubs0segs mem (sp0 - 8 - 8 * Z.of_nat j) (bv_unsigned (getr regs0 r)).
Definition af_stk_chunks (k : nat) : list YP09.chunk :=
map (fun j => mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (k + j) 0))) (seq 0 8).
Definition af_Rstk (k : nat) : YP09.region := YP09.mkRegion (Some 2%nat) 0 64 0 64 (af_stk_chunks k).
Definition af_untouched (regs0 regs1 : bvmap 5 word) : Prop :=
getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\ getr regs1 23 = getr regs0 23 /\ getr regs1 24 = getr regs0 24 /\
getr regs1 25 = getr regs0 25 /\ getr regs1 26 = getr regs0 26 /\ getr regs1 27 = getr regs0 27.
Lemma af_saved_vals_nth : forall regs0 j r,
nth_error AF_SAVED j = Some r -> nth_error (af_saved_vals regs0) j = Some (bv_unsigned (getr regs0 r)).
Proof using.
intros regs0 j r H. unfold af_saved_vals, AF_ATOMS. rewrite nth_error_map, nth_error_app1, H; [reflexivity|].
apply (proj1 (nth_error_Some AF_SAVED j)). rewrite H. discriminate.
Qed.
Lemma af_saved_vals_nth_inv : forall regs0 j v,
nth_error (af_saved_vals regs0) j = Some v -> exists r : reg, nth_error AF_ATOMS j = Some r /\ v = bv_unsigned (getr regs0 r).
Proof using.
intros regs0 j v H. unfold af_saved_vals in H. rewrite nth_error_map in H.
destruct (nth_error AF_ATOMS j) as [r|]; [|discriminate]. cbn in H. injection H as <-. exists r. auto.
Qed.
Lemma u64_range_getr : forall (regs : bvmap 5 word) r, 0 <= bv_unsigned (getr regs r) < 2 ^ 64.
Proof using. intros. pose proof (bv_unsigned_in_range 64 (getr regs r)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Section t.
Variable E : env.
Lemma af_Rstk_ok : forall mem sp0 regs0 k,
bv_unsigned (ew E 2) = sp0 - 64 -> 64 <= sp0 -> sp0 <= 2 ^ 64 ->
af_saved_ok mem sp0 regs0 ->
(forall j v, nth_error (af_saved_vals regs0) j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
(forall a, sp0 - 64 <= a < sp0 -> writable_at ubs0segs mem a) ->
region_ok ubs0segs E mem (af_Rstk k).
Proof using.
intros mem sp0 regs0 k H2 Hlo Hhi HS HK Hw.
unfold af_Rstk, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite H2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
unfold af_stk_chunks. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
destruct (nth_error AF_SAVED j) as [r|] eqn:Hr.
2:{ exfalso. apply nth_error_None in Hr. cbn in Hr. lia. }
eapply (chunk_ok_val _ _ _ _ _ _ _ (bv_unsigned (getr regs0 r))).
- cbn [sv_denot]. rewrite Z.add_0_r, (HK j _ (af_saved_vals_nth regs0 j r Hr)), Z_to_bv_bv_unsigned. reflexivity.
- cbn. apply u64_range_getr.
- cbn. lia.
- apply val_mem_word_mem. replace (sp0 - 64 + (56 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact (HS j r Hr).
Qed.
Lemma af_saved_of_st : forall ss ms k sp0 regs0 rest,
st_ok ubs0segs E ss ms -> ss_mem ss = af_Rstk k :: rest ->
bv_unsigned (ew E 2) = sp0 - 64 ->
(forall j v, nth_error (af_saved_vals regs0) j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
af_saved_ok (ms_mem ms) sp0 regs0.
Proof using.
intros ss ms k sp0 regs0 rest HS Hm H2 HK j r Hr.
pose proof (st_region_chunks ubs0segs E ss ms 0 (af_Rstk k) 2%nat (sp0 - 64) HS ltac:(rewrite Hm; reflexivity) eq_refl H2) as Hcs.
cbn [r_chunks af_Rstk] in Hcs. unfold af_stk_chunks in Hcs.
assert (Hj : (j < 8)%nat) by (apply (proj1 (nth_error_Some AF_SAVED j)); rewrite Hr; discriminate).
pose proof (proj1 (Forall_forall _ _) Hcs (mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (k + j) 0)))
ltac:(apply in_map_iff; exists j; split; [reflexivity | apply in_seq; lia])) as Hc.
apply val_mem_word_mem. replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 - 64 + (56 - 8 * Z.of_nat j)) by lia.
eapply (val_of_chunk_ok ubs0segs E (ms_mem ms) (sp0 - 64) _ 8%N); [exact Hc | | cbn; apply u64_range_getr | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, (HK j _ (af_saved_vals_nth regs0 j r Hr)), Z_to_bv_bv_unsigned. reflexivity.
Qed.
End t.
Lemma af_saved_ok_kept : forall m m' sp0 regs0,
af_saved_ok m sp0 regs0 -> (forall a, sp0 - 64 <= a < sp0 -> mbyte ubs0segs m' a = mbyte ubs0segs m a) -> af_saved_ok m' sp0 regs0.
Proof using.
intros m m' sp0 regs0 H Hf j r Hr k Hk.
assert (Hj : (j < 8)%nat) by (apply (proj1 (nth_error_Some AF_SAVED j)); rewrite Hr; discriminate).
rewrite Hf by lia. apply (H j r Hr). exact Hk.
Qed.
Definition A_CF : nat := 44.
Definition A_G : nat := 51.
Definition A_M : nat := 68.
Definition litsG (p0 p1 p2 : option Z) (ih : option Z) : list (option Z) :=
[p0; p1; p2; None; Some ubs0_D_str_tmp_out_gif; None; None; None; None; None; None; Some 0; Some 0; None; None; None; ih].
Definition af_Rg (p0 p1 p2 ih : option Z) : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF 51 (litsG p0 p1 p2 ih)).
Definition pin_ok (p : option Z) (v : Z) : Prop := match p with Some z => z = v | None => True end.
Lemma litsG_ok : forall s p0 p1 p2 ih,
pin_ok p0 (frame_ptr (nth 0 (cg_frames s) None)) -> pin_ok p1 (frame_ptr (nth 1 (cg_frames s) None)) ->
pin_ok p2 (frame_ptr (nth 2 (cg_frames s) None)) -> pin_ok ih (cg_ihead s) ->
forall j z, nth_error (litsG p0 p1 p2 ih) j = Some (Some z) -> nth_error (cgif_vals s) j = Some z.
Proof using.
intros s p0 p1 p2 ih H0 H1 H2 Hih j z Hj.
destruct p0 as [z0|]; destruct p1 as [z1|]; destruct p2 as [z2|]; destruct ih as [zi|]; cbn in H0, H1, H2, Hih; subst;
do 17 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]); destruct j; discriminate Hj.
Qed.
Definition af_Rcf : YP09.region := YP09.mkRegion (Some 9%nat) 0 32 0 0 (obj_chunks_gen LAY_FrameConfig 44 []).
Definition af_Rfr (n k : nat) : YP09.region := YP09.mkRegion (Some n) 0 40 0 40 (obj_chunks_gen LAY_Frame k []).
Definition af_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + ADDFRAME_STK - 64) (2^63 - 64) 4); (8%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(9%nat, mkAF CEIL_MIN (2^63 - 32) 3) ].
Section u.
Variable segs : list Segment.
Lemma obj_at_of_fields : forall mem a lay vals,
length vals = length lay ->
(forall j f v, nth_error lay j = Some f -> nth_error vals j = Some v -> field_ok segs mem a f v) ->
obj_at segs mem a lay vals.
Proof using.
intros mem a lay. induction lay as [|f lay IH]; intros [|v vals] Hlen HF; cbn in Hlen |- *; try discriminate; [exact I|].
split; [exact (HF 0%nat f v eq_refl eq_refl)|].
apply IH; [lia|]. intros j f' v' Hf Hv. exact (HF (S j) f' v' Hf Hv).
Qed.
Lemma obj_at_fields : forall mem a lay vals,
obj_at segs mem a lay vals ->
forall j f v, nth_error lay j = Some f -> nth_error vals j = Some v -> field_ok segs mem a f v.
Proof using. intros mem a lay vals H j f v Hf Hv. eapply obj_at_nth; eauto. Qed.
Lemma st_field : forall E ss ms i rg p a off (n : N) e v,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
field_ok segs (ms_mem ms) a (off, n) v.
Proof using.
intros E ss ms i rg p a off n e v HS Hi Hb Hin Hp He Hv Hn. split; [|exact Hv].
cbn [fst snd]. eapply st_chunk_val; eauto.
Qed.
Lemma st_field_low : forall E ss ms i rg p a off (n : N) e (m : Z),
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> Z.of_N n <= 8 -> m = 2 ^ (8 * Z.of_N n) ->
field_ok segs (ms_mem ms) a (off, n) (U E e mod m).
Proof using.
intros E ss ms i rg p a off n e m HS Hi Hb Hin Hp Hn ->.
pose proof (st_region_chunks segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
split; cbn [fst snd].
- unfold U. exact (val_mem_low_of_chunk segs E (ms_mem ms) a off n e Hc Hn).
- apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
Lemma field_byte_any : forall mem a off,
present mem (a + off) -> field_ok ubs0segs mem a (off, 1%N) (byte_at mem (a + off)).
Proof using.
intros mem a off Hp. split; cbn [fst snd]; [apply byte_at_val; exact Hp|].
change (2 ^ (8 * 1)) with 256. apply byte_at_range.
Qed.
End u.
Lemma af_frames_blocks_ptr_in : forall N fs f, In (Some f) fs -> In (fr_ptr f, FRAME_SIZE) (frames_blocks N fs).
Proof using. intros N fs f H. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact H | left; reflexivity]. Qed.
Lemma perm_frame_front : forall {X} (g r x i : X) (pal F1 pf F2 rest : list X),
Permutation (g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest) (x :: g :: r :: (pal ++ F1 ++ i :: pf ++ F2) ++ rest).
Proof using.
intros.
assert (E1 : g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest = (g :: r :: pal ++ F1) ++ x :: ((i :: pf ++ F2) ++ rest)).
{ cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
assert (E2 : x :: g :: r :: (pal ++ F1 ++ i :: pf ++ F2) ++ rest = x :: (g :: r :: pal ++ F1) ++ ((i :: pf ++ F2) ++ rest)).
{ cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
rewrite E1, E2. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma perm_frame_frontF : forall {X} (g r fl x i : X) (pal F1 pf F2 rest : list X),
Permutation (g :: r :: fl :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest) (x :: g :: r :: fl :: (pal ++ F1 ++ i :: pf ++ F2) ++ rest).
Proof using.
intros. change (g :: r :: fl :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest) with (g :: r :: ((fl :: pal) ++ F1 ++ x :: i :: pf ++ F2) ++ rest).
change (x :: g :: r :: fl :: (pal ++ F1 ++ i :: pf ++ F2) ++ rest) with (x :: g :: r :: ((fl :: pal) ++ F1 ++ i :: pf ++ F2) ++ rest).
apply perm_frame_front.
Qed.
Section a0.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Lemma af_cgif_geom : forall L A m md g s N rest,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
(4096 <= cg_raw s /\ cg_raw s + RAW_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= cg_raw s \/ cg_raw s + RAW_SIZE <= g)) /\
(forall f, In (Some f) (cg_frames s) -> 4096 <= fr_ptr f /\ fr_ptr f + FRAME_SIZE <= alloc_ceiling /\ (g + CGIF_SIZE <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= g)) /\
(4096 <= g /\ g + CGIF_SIZE <= alloc_ceiling /\ g mod 16 = 0).
Proof using LAWS.
intros L A m md g s N rest HH HB.
assert (Hsub : forall x, In x (cgif_blocks g s N) -> In x (blocks L A)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hx. }
assert (Hsep : forall y, In y ((cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) :: pal_blocks s ++ frames_blocks N (cg_frames s)) -> g + CGIF_SIZE <= fst y \/ fst y + snd y <= g).
{ intros y Hy. apply (heap_sep_perm _ _ LAWS L A m md (g, CGIF_SIZE) (((cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) :: pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest) y HH).
- exact HB.
- apply in_app_iff. left. exact Hy. }
split; [|split].
- destruct (blocks_range _ _ LAWS L A m md (cg_raw s) RAW_SIZE HH (Hsub _ ltac:(right; left; reflexivity))) as [R0 R1].
pose proof (Hsep (cg_raw s, RAW_SIZE) ltac:(left; reflexivity)) as Hs. cbn [fst snd] in Hs. unfold RAW_SIZE, CGIF_SIZE in *. lia.
- intros f Hin. pose proof (af_frames_blocks_ptr_in N (cg_frames s) f Hin) as Hm.
destruct (blocks_range _ _ LAWS L A m md (fr_ptr f) FRAME_SIZE HH (Hsub _ ltac:(right; right; right; apply in_app_iff; right; exact Hm))) as [R0 R1].
pose proof (Hsep (fr_ptr f, FRAME_SIZE) ltac:(right; right; apply in_app_iff; right; exact Hm)) as Hs. cbn [fst snd] in Hs. lia.
- exact (heap_blocks_range _ _ LAWS L A m md g CGIF_SIZE HH (Hsub _ ltac:(left; reflexivity)) ltac:(unfold CGIF_SIZE; lia)).
Qed.
Lemma af_cgif_geom0 : forall L A m md g s N rest,
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
- intros f Hin. pose proof (af_frames_blocks_ptr_in N (cg_frames s) f Hin) as Hm.
destruct (blocks_range _ _ LAWS L A m md (fr_ptr f) FRAME_SIZE HH (Hsub _ ltac:(right; right; apply in_app_iff; right; exact Hm))) as [R0 R1].
pose proof (Hsep (fr_ptr f, FRAME_SIZE) ltac:(right; apply in_app_iff; right; exact Hm)) as Hs. cbn [fst snd] in Hs. lia.
- exact (heap_blocks_range _ _ LAWS L A m md g CGIF_SIZE HH (Hsub _ ltac:(left; reflexivity)) ltac:(unfold CGIF_SIZE; lia)).
Qed.
Lemma af_frame_geom : forall L A m md g s N rest f,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks g s N ++ rest) -> In (Some f) (cg_frames s) ->
In (fr_ptr f, FRAME_SIZE) (blocks L A) /\ In (fr_img f, N) (blocks L A) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) (blocks L A)).
Proof using API.
intros L A m md g s N rest f HH HB Hin.
assert (Hsub : forall x, In x (frame_blocks N f) -> In x (blocks L A)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left.
destruct x as [b n]. apply (frame_blocks_in_cgif g s N f b n Hin Hx). }
split; [apply Hsub; left; reflexivity|]. split; [apply Hsub; right; left; reflexivity|].
intros Ha. apply Hsub. unfold frame_blocks. right. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
Lemma af_frame_geom0 : forall L A m md g s N rest f,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) -> In (Some f) (cg_frames s) ->
In (fr_ptr f, FRAME_SIZE) (blocks L A) /\ In (fr_img f, N) (blocks L A) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) (blocks L A)).
Proof using API.
intros L A m md g s N rest f HH HB Hin.
assert (Hsub : forall x, In x (frame_blocks N f) -> In x (blocks L A)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left.
destruct x as [b n]. apply (frame_blocks_in_cgif0 g s N f b n Hin Hx). }
split; [apply Hsub; left; reflexivity|]. split; [apply Hsub; right; left; reflexivity|].
intros Ha. apply Hsub. unfold frame_blocks. right. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
Lemma af_raw_frame_sep : forall L A m md g s N rest f,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks g s N ++ rest) -> In (Some f) (cg_frames s) ->
cg_raw s + RAW_SIZE <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= cg_raw s.
Proof using LAWS.
intros L A m md g s N rest f HH HB Hin.
pose proof (af_frames_blocks_ptr_in N (cg_frames s) f Hin) as Hm.
assert (HB' : Permutation (blocks L A) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: ((cg_file s, FILE_BLOCK) :: pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest)).
{ eapply Permutation_trans; [exact HB|]. unfold cgif_blocks. cbn [app]. apply perm_swap. }
pose proof (heap_sep_perm _ _ LAWS L A m md (cg_raw s, RAW_SIZE) _ (fr_ptr f, FRAME_SIZE) HH HB'
ltac:(right; apply in_app_iff; left; right; apply in_app_iff; right; exact Hm)) as Hs.
cbn [fst snd] in Hs. exact Hs.
Qed.
Lemma af_raw_frame_sep0 : forall L A m md g s N rest f,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) -> In (Some f) (cg_frames s) ->
cg_raw s + RAW_SIZE <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= cg_raw s.
Proof using LAWS.
intros L A m md g s N rest f HH HB Hin.
pose proof (af_frames_blocks_ptr_in N (cg_frames s) f Hin) as Hm.
assert (HB' : Permutation (blocks L A) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest)).
{ eapply Permutation_trans; [exact HB|]. unfold cgif_blocks0. cbn [app]. apply perm_swap. }
pose proof (heap_sep_perm _ _ LAWS L A m md (cg_raw s, RAW_SIZE) _ (fr_ptr f, FRAME_SIZE) HH HB'
ltac:(right; apply in_app_iff; left; apply in_app_iff; right; exact Hm)) as Hs.
cbn [fst snd] in Hs. exact Hs.
Qed.
Lemma af_frames_sep : forall L A m md g s N rest j1 j2 f1 f2,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
nth_error (cg_frames s) j1 = Some (Some f1) -> nth_error (cg_frames s) j2 = Some (Some f2) -> j1 <> j2 ->
fr_ptr f1 + FRAME_SIZE <= fr_ptr f2 \/ fr_ptr f2 + FRAME_SIZE <= fr_ptr f1.
Proof using LAWS.
intros L A m md g s N rest j1 j2 f1 f2 HH HB H1 H2 Hne.
destruct (nth_error_split _ _ H1) as (l1 & l2 & Hfr & Hl1).
assert (Hf2 : In (Some f2) (l1 ++ l2)).
{ rewrite Hfr in H2. destruct (Nat.lt_ge_cases j2 (length l1)) as [Hlt|Hge].
- apply in_app_iff. left. rewrite nth_error_app1 in H2 by exact Hlt. eapply nth_error_In. exact H2.
- apply in_app_iff. right. rewrite nth_error_app2 in H2 by exact Hge.
destruct (j2 - length l1)%nat as [|k] eqn:Hk; [lia|]. cbn in H2. eapply nth_error_In. exact H2. }
assert (HP : Permutation (cgif_blocks g s N ++ rest)
((fr_ptr f1, FRAME_SIZE) :: (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_img f1, N) :: (if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]) ++ frames_blocks N l2) ++ rest)).
{ unfold cgif_blocks. rewrite Hfr, frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). unfold frame_blocks at 1.
apply perm_frame_frontF. }
pose proof (heap_sep_perm _ _ LAWS L A m md (fr_ptr f1, FRAME_SIZE) _ (fr_ptr f2, FRAME_SIZE) HH (Permutation_trans HB HP)) as Hs.
cbn [fst snd] in Hs. apply Hs. right. right. right. apply in_app_iff. left. apply in_app_iff. right.
apply in_app_iff in Hf2 as [Hf2|Hf2].
- apply in_app_iff. left. apply af_frames_blocks_ptr_in. exact Hf2.
- apply in_app_iff. right. right. apply in_app_iff. right. apply af_frames_blocks_ptr_in. exact Hf2.
Qed.
Lemma af_frames_sep0 : forall L A m md g s N rest j1 j2 f1 f2,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) ->
nth_error (cg_frames s) j1 = Some (Some f1) -> nth_error (cg_frames s) j2 = Some (Some f2) -> j1 <> j2 ->
fr_ptr f1 + FRAME_SIZE <= fr_ptr f2 \/ fr_ptr f2 + FRAME_SIZE <= fr_ptr f1.
Proof using LAWS.
intros L A m md g s N rest j1 j2 f1 f2 HH HB H1 H2 Hne.
destruct (nth_error_split _ _ H1) as (l1 & l2 & Hfr & Hl1).
assert (Hf2 : In (Some f2) (l1 ++ l2)).
{ rewrite Hfr in H2. destruct (Nat.lt_ge_cases j2 (length l1)) as [Hlt|Hge].
- apply in_app_iff. left. rewrite nth_error_app1 in H2 by exact Hlt. eapply nth_error_In. exact H2.
- apply in_app_iff. right. rewrite nth_error_app2 in H2 by exact Hge.
destruct (j2 - length l1)%nat as [|k] eqn:Hk; [lia|]. cbn in H2. eapply nth_error_In. exact H2. }
assert (HP : Permutation (cgif_blocks0 g s N ++ rest)
((fr_ptr f1, FRAME_SIZE) :: (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_img f1, N) :: (if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]) ++ frames_blocks N l2) ++ rest)).
{ unfold cgif_blocks0. rewrite Hfr, frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). unfold frame_blocks at 1.
apply perm_frame_front. }
pose proof (heap_sep_perm _ _ LAWS L A m md (fr_ptr f1, FRAME_SIZE) _ (fr_ptr f2, FRAME_SIZE) HH (Permutation_trans HB HP)) as Hs.
cbn [fst snd] in Hs. apply Hs. right. right. apply in_app_iff. left. apply in_app_iff. right.
apply in_app_iff in Hf2 as [Hf2|Hf2].
- apply in_app_iff. left. apply af_frames_blocks_ptr_in. exact Hf2.
- apply in_app_iff. right. right. apply in_app_iff. right. apply af_frames_blocks_ptr_in. exact Hf2.
Qed.
End a0.
Section b0.
Variable segs : list Segment.
Definition in_wins (wins : list (Z * Z)) (i : Z) : bool := existsb (fun w => (fst w <=? i) && (i <? snd w)) wins.
Fixpoint lay_upd_ok (lay : layout_t) (j0 : nat) (js : list nat) (wins : list (Z * Z)) : bool :=
match lay with
| [] => true
| f :: lay' =>
(existsb (Nat.eqb j0) js
|| forallb (fun i => negb (in_wins wins (fst f + Z.of_nat i))) (seq 0 (N.to_nat (snd f))))
&& lay_upd_ok lay' (S j0) js wins
end.
Lemma field_ok_kept : forall m m' a f v,
field_ok segs m a f v -> (forall i, 0 <= i < Z.of_N (snd f) -> mbyte segs m' (a + fst f + i) = mbyte segs m (a + fst f + i)) ->
field_ok segs m' a f v.
Proof using.
intros m m' a [o w] v [Hv Hr] Hk. split; [|exact Hr]. cbn [fst snd] in *.
intros k Hk'. rewrite Hk by lia. apply Hv. exact Hk'.
Qed.
Lemma in_wins_false : forall wins i, in_wins wins i = false -> forall w, In w wins -> ~ (fst w <= i < snd w).
Proof using.
intros wins i H w Hw Hi. unfold in_wins in H.
assert (Ht : existsb (fun w => (fst w <=? i) && (i <? snd w)) wins = true).
{ apply existsb_exists. exists w. split; [exact Hw|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite Ht in H. discriminate.
Qed.
Lemma in_wins_cons_false : forall lo hi wins i, in_wins ((lo, hi) :: wins) i = false -> (i < lo \/ hi <= i) /\ in_wins wins i = false.
Proof using.
intros lo hi wins i H. unfold in_wins in H. cbn [existsb fst snd] in H. apply orb_false_elim in H as [H1 H2].
split; [|exact H2]. destruct (Z.leb_spec lo i); destruct (Z.ltb_spec i hi); cbn in H1; try discriminate; lia.
Qed.
Lemma obj_at_upd_gen : forall m m' a lay j0 vals vals' js wins,
obj_at segs m a lay vals -> lay_upd_ok lay j0 js wins = true -> length vals' = length vals ->
(forall i, (exists f, In f lay /\ fst f <= i < fst f + Z.of_N (snd f)) -> in_wins wins i = false -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
(forall j f v', In (j0 + j)%nat js -> nth_error lay j = Some f -> nth_error vals' j = Some v' -> field_ok segs m' a f v') ->
(forall j, ~ In (j0 + j)%nat js -> nth_error vals' j = nth_error vals j) ->
obj_at segs m' a lay vals'.
Proof using.
intros m m' a lay. induction lay as [|f lay IH]; intros j0 [|v vals] [|v' vals'] js wins Hobj Hok Hlen Hkeep Hupd Hsame;
cbn in Hobj, Hlen |- *; first [exact I | discriminate Hlen | destruct Hobj; fail | idtac].
cbn [lay_upd_ok] in Hok. apply andb_prop in Hok as [Hf Hok].
destruct Hobj as [Hfv Hobj]. split.
- destruct (existsb (Nat.eqb j0) js) eqn:Hin.
+ apply existsb_exists in Hin as (j' & Hj' & Heq). apply Nat.eqb_eq in Heq. subst j'.
apply (Hupd 0%nat f v'); [rewrite Nat.add_0_r; exact Hj' | reflexivity | reflexivity].
+ cbn [orb] in Hf.
assert (Hv' : Some v' = Some v).
{ change (nth_error (v' :: vals') 0 = nth_error (v :: vals) 0). apply Hsame. rewrite Nat.add_0_r.
intros Hj. assert (existsb (Nat.eqb j0) js = true) by (apply existsb_exists; exists j0; split; [exact Hj | apply Nat.eqb_refl]). congruence. }
injection Hv' as ->. apply (field_ok_kept m m' a f v Hfv).
intros i Hi. replace (a + fst f + i) with (a + (fst f + i)) by lia. apply Hkeep.
* exists f. split; [left; reflexivity | lia].
* pose proof (proj1 (forallb_forall _ _) Hf (Z.to_nat i) ltac:(apply in_seq; lia)) as Hb. cbn beta in Hb.
rewrite Z2Nat.id in Hb by lia. destruct (in_wins wins (fst f + i)); [discriminate | reflexivity].
- apply (IH (S j0) vals vals' js wins Hobj Hok ltac:(lia)).
+ intros i (f' & Hf' & Hi) Hw. apply Hkeep; [| exact Hw]. exists f'. split; [right; exact Hf' | exact Hi].
+ intros j f' v'' Hj Hf' Hv''. apply (Hupd (S j) f' v''); [rewrite Nat.add_succ_r; exact Hj | exact Hf' | exact Hv''].
+ intros j Hj. apply (Hsame (S j)). rewrite Nat.add_succ_r. exact Hj.
Qed.
Lemma obj_at_upd : forall m m' a lay sz vals vals' js wins,
obj_at segs m a lay vals -> lay_inside lay sz = true -> lay_upd_ok lay 0 js wins = true -> length vals' = length vals ->
(forall i, 0 <= i < sz -> in_wins wins i = false -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
(forall j f v', In j js -> nth_error lay j = Some f -> nth_error vals' j = Some v' -> field_ok segs m' a f v') ->
(forall j, ~ In j js -> nth_error vals' j = nth_error vals j) ->
obj_at segs m' a lay vals'.
Proof using.
intros m m' a lay sz vals vals' js wins Hobj Hin Hok Hlen Hkeep Hupd Hsame.
apply (obj_at_upd_gen m m' a lay 0 vals vals' js wins Hobj Hok Hlen).
- intros i (f & Hf & Hi) Hw. apply Hkeep; [|exact Hw].
unfold lay_inside in Hin. pose proof (proj1 (forallb_forall _ _) Hin f Hf) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
- exact Hupd.
- exact Hsame.
Qed.
End b0.
Definition chunks_between (lo hi : Z) (cs : list YP09.chunk) : list YP09.chunk :=
List.filter (fun c => (lo <=? c_off c) && (c_off c <? hi)) cs.
Lemma region_ok_part : forall segs E mem b lo0 hi0 wlo0 whi0 cs lo hi wlo whi,
region_ok segs E mem (YP09.mkRegion b lo0 hi0 wlo0 whi0 cs) -> lo0 <= lo -> hi <= hi0 ->
(forall i, wlo <= i < whi -> writable_at segs mem (base_val E b + i)) ->
region_ok segs E mem (YP09.mkRegion b lo hi wlo whi (chunks_between lo hi cs)).
Proof using.
intros segs E mem b lo0 hi0 wlo0 whi0 cs lo hi wlo whi (R1 & R2 & R3 & R4) Hlo Hhi Hw.
unfold region_ok in *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks] in *.
split; [lia|]. split; [lia|]. split; [exact Hw|].
unfold chunks_between. apply incl_Forall with (l1 := cs); [apply incl_filter | exact R4].
Qed.
Definition af_Rg_part (lo hi wlo whi : Z) (p0 p1 p2 ih : option Z) : YP09.region :=
YP09.mkRegion (Some 8%nat) lo hi wlo whi (chunks_between lo hi (obj_chunks_gen LAY_CGIF 51 (litsG p0 p1 p2 ih))).
Definition af_Rfr_part (n k : nat) (lo hi wlo whi : Z) : YP09.region :=
YP09.mkRegion (Some n) lo hi wlo whi (chunks_between lo hi (obj_chunks_gen LAY_Frame k [])).
Lemma lay_inside_FrameConfig : lay_inside LAY_FrameConfig 32 = true.
Proof using. reflexivity. Qed.
Definition upd_frame (s : cgif_st) (i : nat) (f' : frame_st) : cgif_st := set_frames s (list_set (cg_frames s) i (Some f')).
Lemma nth_list_set_same : forall {X} (l : list X) i x d, (i < length l)%nat -> nth i (list_set l i x) d = x.
Proof using. intros X l. induction l as [|y l IH]; intros [|i] x d Hi; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.
Lemma In_list_set : forall {X} (l : list X) i x y, In y (list_set l i x) -> y = x \/ exists j, nth_error l j = Some y /\ j <> i.
Proof using.
intros X l. induction l as [|z l IH]; intros [|i] x y H; cbn in H.
- destruct H.
- destruct H.
- destruct H as [<-|H]; [left; reflexivity|]. right. destruct (In_nth_error _ _ H) as [j Hj]. exists (S j). split; [exact Hj | lia].
- destruct H as [<-|H]; [right; exists 0%nat; split; [reflexivity | lia]|].
destruct (IH i x y H) as [->|(j & Hj & Hne)]; [left; reflexivity|]. right. exists (S j). split; [exact Hj | lia].
Qed.
Lemma cgif_vals_upd_frame : forall s i f f',
nth_error (cg_frames s) i = Some (Some f) -> fr_ptr f' = fr_ptr f -> cgif_vals (upd_frame s i f') = cgif_vals s.
Proof using.
intros s i f f' Hi Hp. unfold upd_frame. rewrite cgif_vals_set_frames. unfold cgif_vals.
assert (E : forall k, frame_ptr (nth k (list_set (cg_frames s) i (Some f')) None) = frame_ptr (nth k (cg_frames s) None)).
{ intros k. destruct (Nat.eq_dec k i) as [->|Hne].
- rewrite nth_list_set_same by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
rewrite (nth_error_nth _ _ _ Hi). cbn. exact Hp.
- rewrite nth_list_set_other by lia. reflexivity. }
rewrite !E. reflexivity.
Qed.
Lemma frames_blocks_upd : forall N l i f f',
nth_error l i = Some (Some f) -> frame_blocks N f' = frame_blocks N f -> frames_blocks N (list_set l i (Some f')) = frames_blocks N l.
Proof using.
intros N l. induction l as [|o l IH]; intros [|i] f f' Hi Hb; cbn in Hi; try discriminate.
- injection Hi as ->. cbn [list_set]. rewrite !frames_blocks_cons_some. rewrite Hb. reflexivity.
- cbn [list_set]. unfold frames_blocks in *. cbn [flat_map]. rewrite (IH i f f' Hi Hb). reflexivity.
Qed.
Lemma cgif_blocks_upd_frame : forall g s N i f f',
nth_error (cg_frames s) i = Some (Some f) -> frame_blocks N f' = frame_blocks N f -> cgif_blocks g (upd_frame s i f') N = cgif_blocks g s N.
Proof using.
intros g s N i f f' Hi Hb. unfold upd_frame. rewrite cgif_blocks_set_frames. unfold cgif_blocks.
rewrite (frames_blocks_upd N _ i f f' Hi Hb). reflexivity.
Qed.
Lemma cgif_wf_upd_frame : forall s N i f f',
cgif_wf s N -> nth_error (cg_frames s) i = Some (Some f) -> frame_wf (cg_attr s) f' -> cgif_wf (upd_frame s i f') N.
Proof using.
intros s N i f f' Hwf Hi Hf'. pose proof Hwf as (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf).
unfold upd_frame, set_frames. apply cgif_wf_intro; [exact Hwf | rewrite length_list_set; exact Hlen | |].
- destruct Hih as [H1|[H2 Hn1]]; [left; exact H1 | right; split; [exact H2|]].
destruct (Nat.eq_dec i 1) as [->|Hne].
+ rewrite nth_list_set_same by (rewrite Hlen; lia). discriminate.
+ rewrite nth_list_set_other by lia. exact Hn1.
- intros x Hx. destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hne)].
+ injection Hx' as ->. exact Hf'.
+ apply Hfwf. eapply nth_error_In. exact Hj.
Qed.
Lemma same_geom_upd_frame : forall s s0 i f', same_geom s s0 -> same_geom (upd_frame s i f') s0.
Proof using. intros s s0 i f' H. exact H. Qed.
Lemma frame_wf_fields : forall gattr f f',
frame_wf gattr f -> fr_attr f' = fr_attr f -> fr_disp f' = fr_disp f -> frame_wf gattr f'.
Proof using. intros gattr f f' [H1 H2] Ha Hd. split; [rewrite Ha; exact H1 | rewrite Hd; exact H2]. Qed.
Lemma frames_at_upd : forall m m' s i (f : option frame_st) f',
(forall x, In (Some x) (cg_frames s) -> obj_at ubs0segs m (fr_ptr x) LAY_Frame (frame_vals x)) ->
nth_error (cg_frames s) i = Some f ->
obj_at ubs0segs m' (fr_ptr f') LAY_Frame (frame_vals f') ->
(forall j x, nth_error (cg_frames s) j = Some (Some x) -> j <> i ->
forall k, 0 <= k < FRAME_SIZE -> mbyte ubs0segs m' (fr_ptr x + k) = mbyte ubs0segs m (fr_ptr x + k)) ->
forall x, In (Some x) (cg_frames (upd_frame s i f')) -> obj_at ubs0segs m' (fr_ptr x) LAY_Frame (frame_vals x).
Proof using.
intros m m' s i f f' Hfr Hi Hnew Hkept x Hx. unfold upd_frame, set_frames in Hx. cbn [cg_frames] in Hx.
destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hne)].
- injection Hx' as ->. exact Hnew.
- eapply obj_at_transport_range; [apply Hfr; eapply nth_error_In; exact Hj | exact (proj1 LAY_Frame_ok) |].
intros k Hk. apply (Hkept j x Hj Hne k Hk).
Qed.
Lemma nth_error_upd_frame_same : forall s i (f : option frame_st) f', nth_error (cg_frames s) i = Some f ->
nth_error (cg_frames (upd_frame s i f')) i = Some (Some f').
Proof using.
intros s i f f' H. unfold upd_frame, set_frames. cbn [cg_frames]. apply nth_error_list_set_same.
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma nth_error_upd_frame_other : forall s i j f', j <> i -> nth_error (cg_frames (upd_frame s i f')) j = nth_error (cg_frames s) j.
Proof using. intros s i j f' H. unfold upd_frame, set_frames. cbn [cg_frames]. apply nth_error_list_set_other. lia. Qed.
Lemma nth_upd_frame_other : forall s i j f' d, j <> i -> nth j (cg_frames (upd_frame s i f')) d = nth j (cg_frames s) d.
Proof using. intros s i j f' d H. unfold upd_frame, set_frames. cbn [cg_frames]. apply nth_list_set_other. lia. Qed.
Lemma cg_ihead_upd_frame : forall s i f', cg_ihead (upd_frame s i f') = cg_ihead s.
Proof using. intros. reflexivity. Qed.
Lemma cg_attr_upd_frame : forall s i f', cg_attr (upd_frame s i f') = cg_attr s.
Proof using. intros. reflexivity. Qed.
Lemma cg_raw_upd_frame : forall s i f', cg_raw (upd_frame s i f') = cg_raw s.
Proof using. intros. reflexivity. Qed.
Lemma frames_at_upd2 : forall m m' s i1 i2 (f1 : option frame_st) f1' (f2 : option frame_st) f2',
(forall x, In (Some x) (cg_frames s) -> obj_at ubs0segs m (fr_ptr x) LAY_Frame (frame_vals x)) ->
nth_error (cg_frames s) i1 = Some f1 -> nth_error (cg_frames s) i2 = Some f2 -> i1 <> i2 ->
obj_at ubs0segs m' (fr_ptr f1') LAY_Frame (frame_vals f1') ->
obj_at ubs0segs m' (fr_ptr f2') LAY_Frame (frame_vals f2') ->
(forall j x, nth_error (cg_frames s) j = Some (Some x) -> j <> i1 -> j <> i2 ->
forall k, 0 <= k < FRAME_SIZE -> mbyte ubs0segs m' (fr_ptr x + k) = mbyte ubs0segs m (fr_ptr x + k)) ->
forall x, In (Some x) (cg_frames (upd_frame (upd_frame s i1 f1') i2 f2')) -> obj_at ubs0segs m' (fr_ptr x) LAY_Frame (frame_vals x).
Proof using.
intros m m' s i1 i2 f1 f1' f2 f2' Hfr H1 H2 Hne Ho1 Ho2 Hkept x Hx.
unfold upd_frame, set_frames in Hx. cbn [cg_frames] in Hx.
destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hj2)]; [injection Hx' as ->; exact Ho2|].
destruct (Nat.eq_dec j i1) as [->|Hj1].
- rewrite nth_error_list_set_same in Hj by (apply (proj1 (nth_error_Some _ _)); rewrite H1; discriminate).
injection Hj as ->. exact Ho1.
- rewrite nth_error_list_set_other in Hj by lia.
eapply obj_at_transport_range; [apply Hfr; eapply nth_error_In; exact Hj | exact (proj1 LAY_Frame_ok) |].
intros k Hk. apply (Hkept j x Hj Hj1 Hj2 k Hk).
Qed.
Lemma cgif_vals_ins_frame : forall s i f', (i < 3)%nat -> length (cg_frames s) = 3%nat ->
cgif_vals (upd_frame s i f') = list_set (cgif_vals s) i (fr_ptr f').
Proof using.
intros s i f' Hi Hlen. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]] eqn:Hfr; cbn in Hlen; try discriminate.
unfold upd_frame. rewrite Hfr. unfold cgif_vals, set_frames. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead].
rewrite Hfr. destruct i as [|[|[|i]]]; try lia; reflexivity.
Qed.
Lemma cgif_blocks_ins_frame : forall g s N i f',
nth_error (cg_frames s) i = Some None ->
Permutation (cgif_blocks g (upd_frame s i f') N) (frame_blocks N f' ++ cgif_blocks g s N).
Proof using.
intros g s N i f' Hi. unfold upd_frame. rewrite cgif_blocks_set_frames. unfold cgif_blocks.
destruct (nth_error_split _ _ Hi) as (l1 & l2 & Hfr & Hl1). rewrite Hfr at 2.
assert (E : list_set (cg_frames s) i (Some f') = l1 ++ Some f' :: l2).
{ rewrite Hfr, <- Hl1. clear. induction l1 as [|y l1 IH]; cbn; [reflexivity | rewrite IH; reflexivity]. }
rewrite E, !frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). cbn [app].
apply Permutation_sym.
change ((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) :: pal_blocks s ++ frames_blocks N l1 ++ frame_blocks N f' ++ frames_blocks N l2)
with (((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) :: pal_blocks s) ++ (frames_blocks N l1 ++ frame_blocks N f' ++ frames_blocks N l2)).
change (frame_blocks N f' ++ (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) :: pal_blocks s ++ frames_blocks N l1 ++ frames_blocks N l2)
with (frame_blocks N f' ++ ((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: (cg_file s, FILE_BLOCK) :: pal_blocks s) ++ (frames_blocks N l1 ++ frames_blocks N l2)).
rewrite (app_assoc (frames_blocks N l1)).
eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_swap_app|].
rewrite <- app_assoc. rewrite (app_assoc (frame_blocks N f')).
eapply Permutation_trans; [apply Permutation_app_swap_app|].
rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_swap_app.
Qed.
Lemma cgif_wf_ins_frame : forall s N i f',
cgif_wf s N -> nth_error (cg_frames s) i = Some None -> frame_wf (cg_attr s) f' -> cgif_wf (upd_frame s i f') N.
Proof using.
intros s N i f' Hwf Hi Hf'. pose proof Hwf as (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf).
unfold upd_frame, set_frames. apply cgif_wf_intro; [exact Hwf | rewrite length_list_set; exact Hlen | |].
- destruct Hih as [H1|[H2 Hn1]]; [left; exact H1 | right; split; [exact H2|]].
destruct (Nat.eq_dec i 1) as [->|Hne].
+ rewrite nth_list_set_same by (rewrite Hlen; lia). discriminate.
+ rewrite nth_list_set_other by lia. exact Hn1.
- intros x Hx. destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hne)].
+ injection Hx' as ->. exact Hf'.
+ apply Hfwf. eapply nth_error_In. exact Hj.
Qed.
Lemma cgif_wf_set_ihead : forall s N ih,
cgif_wf s N -> (ih = 1 \/ (ih = 2 /\ nth 1 (cg_frames s) None <> None)) -> cgif_wf (set_ihead s ih) N.
Proof using.
intros s N ih (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf) H. unfold cgif_wf, set_ihead. cbn. repeat (split; [assumption|]). exact Hfwf.
Qed.
Lemma cgif_blocks_set_ihead : forall g s N ih, cgif_blocks g (set_ihead s ih) N = cgif_blocks g s N.
Proof using. intros. reflexivity. Qed.
Lemma cg_frames_set_ihead : forall s ih, cg_frames (set_ihead s ih) = cg_frames s.
Proof using. intros. reflexivity. Qed.
Lemma cg_raw_set_ihead : forall s ih, cg_raw (set_ihead s ih) = cg_raw s.
Proof using. intros. reflexivity. Qed.
Lemma cg_attr_set_ihead : forall s ih, cg_attr (set_ihead s ih) = cg_attr s.
Proof using. intros. reflexivity. Qed.
Lemma same_geom_set_ihead : forall s s0 ih, same_geom s s0 -> same_geom (set_ihead s ih) s0.
Proof using. intros s s0 ih H. exact H. Qed.
Lemma st_field_byte0 : forall segs E ss ms i rg p a off (n : N) e,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> (1 <= Z.of_N n)%Z -> Z.of_N n <= 8 ->
field_ok segs (ms_mem ms) a (off, 1%N) (U E e mod 256).
Proof using.
intros segs E ss ms i rg p a off n e HS Hi Hb Hin Hp Hn1 Hn.
pose proof (st_region_chunks segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
pose proof (val_mem_low_of_chunk segs E (ms_mem ms) a off n e Hc Hn) as Hv.
split; cbn [fst snd]; [| change (2 ^ (8 * 1)) with 256; apply Z.mod_pos_bound; lia].
intros k Hk. destruct k; [|cbn in Hk; lia]. rewrite (Hv 0%nat) by (pose proof (N_nat_Z n); lia). f_equal.
unfold le_byte. change (8 * Z.of_nat 0) with 0. rewrite !Z.shiftr_0_r. unfold U.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ 8) with 256. rewrite (Z.mod_mod _ 256) by lia. f_equal.
rewrite N_nat_Z. set (M := 2 ^ (8 * Z.of_N n)). set (v := bv_unsigned (sv_denot E e)).
assert (HM : 0 < M) by (subst M; apply Z.pow_pos_nonneg; lia).
rewrite ?(Z.mod_mod v M), ?(Z.mod_mod v 256) by lia.
lazymatch goal with |- v mod 256 = (v mod M) mod 256 => symmetry | |- _ => idtac end. apply Z.mod_mod_divide.
exists (2 ^ (8 * Z.of_N n - 8)). subst M. change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma cgif_vals_flush_upd : forall s i gen' rwcur', cgif_vals (flush_upd s i gen' rwcur') = cgif_vals s.
Proof using. intros. unfold cgif_vals. rewrite !flush_upd_frames_shape. reflexivity. Qed.
Lemma frames_flush_upd1 : forall s o0 f1 o2 gen' rwcur',
cg_frames s = [o0; Some f1; o2] -> cg_frames (flush_upd s 1 gen' rwcur') = [o0; Some (set_fr_gen f1 gen'); o2].
Proof using. intros s o0 f1 o2 gen' rwcur' H. rewrite flush_upd_wf_frames, H. reflexivity. Qed.
Lemma raw_vals_set_frames : forall g s fr, raw_vals g (set_frames s fr) = raw_vals g s.
Proof using. intros. reflexivity. Qed.
Lemma cg_raw_set_frames : forall s fr, cg_raw (set_frames s fr) = cg_raw s.
Proof using. intros. reflexivity. Qed.
Lemma cg_frames_set_frames : forall s fr, cg_frames (set_frames s fr) = fr.
Proof using. intros. reflexivity. Qed.
Lemma perm_g_r_pal_front : forall {X} (g r : X) (pal fb0 fbs Xl : list X),
Permutation (g :: r :: (pal ++ fb0 ++ fbs) ++ Xl) (fb0 ++ g :: r :: (pal ++ fbs) ++ Xl).
Proof using.
intros.
assert (E1 : g :: r :: (pal ++ fb0 ++ fbs) ++ Xl = (g :: r :: pal) ++ fb0 ++ (fbs ++ Xl)).
{ cbn. rewrite <- !app_assoc. reflexivity. }
assert (E2 : fb0 ++ g :: r :: (pal ++ fbs) ++ Xl = fb0 ++ (g :: r :: pal) ++ (fbs ++ Xl)).
{ cbn. rewrite <- !app_assoc. reflexivity. }
rewrite E1, E2. apply Permutation_app_swap_app.
Qed.
Lemma perm_frame0_front : forall g s N f0 o1 o2 X,
cg_frames s = [Some f0; o1; o2] ->
Permutation (cgif_blocks g s N ++ X) (frame_blocks N f0 ++ cgif_blocks g (set_frames s [None; o1; o2]) N ++ X).
Proof using.
intros g s N f0 o1 o2 X H. unfold cgif_blocks. rewrite H. cbn [cg_raw cg_file cg_frames set_frames]. rewrite pal_blocks_set_frames.
rewrite frames_blocks_cons_some, frames_blocks_cons_none. apply (perm_g_r_pal_front _ _ ((cg_file s, FILE_BLOCK) :: pal_blocks s)).
Qed.
Lemma cgif_blocks_shift : forall g s o1 o2 N,
cgif_blocks g (set_frames s [o1; o2; None]) N = cgif_blocks g (set_frames s [None; o1; o2]) N.
Proof using.
intros g s o1 o2 N. unfold cgif_blocks. cbn [cg_raw cg_file cg_frames set_frames]. rewrite !pal_blocks_set_frames.
unfold frames_blocks. cbn [flat_map]. cbn [app]. rewrite !app_nil_r. reflexivity.
Qed.
Lemma cgif_wf_set_frames : forall s N fr,
cgif_wf s N -> length fr = 3%nat ->
(cg_ihead s = 1 \/ (cg_ihead s = 2 /\ nth 1 fr None <> None)) ->
(forall f, In (Some f) fr -> frame_wf (cg_attr s) f) ->
cgif_wf (set_frames s fr) N.
Proof using. intros s N fr Hwf Hl Hi Hf. unfold set_frames. apply cgif_wf_intro; assumption. Qed.
Definition af_AL (regs0 : bvmap 5 word) (cf : list Z) (s : cgif_st) (more : list Z) : list Z :=
af_saved_vals regs0 ++ cf ++ cgif_vals s ++ more.
Definition af_E (regs1 regs0 : bvmap 5 word) (cf : list Z) (s : cgif_st) (more : list Z) : env :=
Ereg regs1 (map (Z_to_bv 64) (af_AL regs0 cf s more) ++ []).
Lemma nth_error_app_len : forall {X} (l1 l2 : list X) j, nth_error (l1 ++ l2) (length l1 + j) = nth_error l2 j.
Proof using. intros X l1 l2 j. rewrite nth_error_app2 by lia. f_equal. lia. Qed.
Section c0.
Variables (regs1 regs0 : bvmap 5 word) (lpal img fattr fgen delay nlp tidx : Z) (s : cgif_st) (more : list Z).
Let cf := [lpal; img; fattr; fgen; delay; nlp; tidx].
Let E := af_E regs1 regs0 cf s more.
Lemma af_HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr.
Proof using cf more regs0 s. intros n rr H. unfold E, af_E. apply ew_Ereg_nat. exact H. Qed.
Lemma af_HA : forall j v, nth_error (af_AL regs0 cf s more) j = Some v -> ew E (32 + j) = Z_to_bv 64 v.
Proof using delay fattr fgen img lpal nlp regs1 tidx. intros j v H. unfold E, af_E. apply Ereg_vals. exact H. Qed.
Lemma af_HK : forall n j v, n = (32 + j)%nat -> nth_error (af_saved_vals regs0) j = Some v -> ew E n = Z_to_bv 64 v.
Proof using cf more regs1 s.
intros n j v -> H. apply af_HA. unfold af_AL. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma af_HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error AF_SAVED j = Some r -> ew E n = getr regs0 r.
Proof using cf more regs1 s. intros n j r Hn Hr. rewrite (af_HK n j _ Hn (af_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. Qed.
Lemma af_HC : forall n j v, n = (44 + j)%nat -> nth_error cf j = Some v -> ew E n = Z_to_bv 64 v.
Proof using delay fattr fgen img lpal more nlp regs0 regs1 s tidx.
intros n j v -> H. replace (44 + j)%nat with (32 + (length (af_saved_vals regs0) + j))%nat by reflexivity.
apply af_HA. unfold af_AL. rewrite nth_error_app_len. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma af_HX : forall n j v, n = (51 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v.
Proof using cf more regs0 regs1.
intros n j v -> H. replace (51 + j)%nat with (32 + (length (af_saved_vals regs0 ++ cf) + j))%nat by reflexivity.
apply af_HA. unfold af_AL. rewrite app_assoc, nth_error_app_len. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma af_HM : forall n j v, n = (68 + j)%nat -> nth_error more j = Some v -> ew E n = Z_to_bv 64 v.
Proof using cf regs0 regs1 s.
intros n j v -> H. replace (68 + j)%nat with (32 + (length (af_saved_vals regs0 ++ cf ++ cgif_vals s) + j))%nat by (rewrite !length_app; reflexivity).
apply af_HA. unfold af_AL. rewrite 2!app_assoc, nth_error_app_len. exact H.
Qed.
Definition cf_facts : list (nat * afact) :=
[ (44%nat, mkAF 0 (2^64 - 1) 0); (45%nat, mkAF 0 (2^64 - 1) 0); (46%nat, mkAF 0 4294967295 0); (47%nat, mkAF 0 4294967295 0);
(48%nat, mkAF 0 65535 0); (49%nat, mkAF 0 65535 0); (50%nat, mkAF 0 255 0) ].
Lemma cf_facts_ok : forall mem cfp, obj_at ubs0segs mem cfp LAY_FrameConfig cf -> atoms_ok E cf_facts.
Proof using delay fattr fgen img lpal more nlp regs0 regs1 s tidx.
intros mem cfp Hobj. pose proof (obj_at_range _ _ _ _ _ Hobj) as R.
cbn [atoms_ok cf_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (2 ^ 0) with 1.
rewrite (af_HC 44 0 lpal eq_refl eq_refl), (af_HC 45 1 img eq_refl eq_refl), (af_HC 46 2 fattr eq_refl eq_refl), (af_HC 47 3 fgen eq_refl eq_refl),
(af_HC 48 4 delay eq_refl eq_refl), (af_HC 49 5 nlp eq_refl eq_refl), (af_HC 50 6 tidx eq_refl eq_refl).
pose proof (R 0%nat lpal eq_refl) as R0. pose proof (R 1%nat img eq_refl) as R1. pose proof (R 2%nat fattr eq_refl) as R2.
pose proof (R 3%nat fgen eq_refl) as R3. pose proof (R 4%nat delay eq_refl) as R4. pose proof (R 5%nat nlp eq_refl) as R5. pose proof (R 6%nat tidx eq_refl) as R6.
cbn [nth snd LAY_FrameConfig Z.of_N] in R0, R1, R2, R3, R4, R5, R6.
rewrite !unsigned_lit_small by lia. rewrite !Z.mod_1_r. repeat split; lia.
Qed.
Lemma af_Rcf_ok : forall mem cfp,
bv_unsigned (ew E 9) = cfp -> 0 <= cfp -> cfp + 32 <= 2 ^ 64 ->
obj_at ubs0segs mem cfp LAY_FrameConfig cf -> region_ok ubs0segs E mem af_Rcf.
Proof using delay fattr fgen img lpal more nlp regs0 regs1 s tidx.
intros mem cfp H9 Hlo Hhi Hobj. unfold af_Rcf.
eapply (region_ok_obj_gen ubs0segs E mem 9 cfp 32 0 0 LAY_FrameConfig cf 44 []);
[exact H9 | lia | lia | exact Hobj | reflexivity | | intros [|j] z Hz; discriminate Hz | intros i Hi; lia].
intros j v Hj. apply (af_HC (44 + j) j v eq_refl Hj).
Qed.
Lemma af_Rg_ok : forall mem g p0 p1 p2 ih,
bv_unsigned (ew E 8) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs0segs mem g LAY_CGIF (cgif_vals s) ->
pin_ok p0 (frame_ptr (nth 0 (cg_frames s) None)) -> pin_ok p1 (frame_ptr (nth 1 (cg_frames s) None)) ->
pin_ok p2 (frame_ptr (nth 2 (cg_frames s) None)) -> pin_ok ih (cg_ihead s) ->
region_ok ubs0segs E mem (af_Rg p0 p1 p2 ih).
Proof using cf more regs0 regs1.
intros mem g p0 p1 p2 ih H8 Hlo Hhi Hobj P0 P1 P2 Pi. unfold af_Rg.
eapply (region_ok_obj_gen ubs0segs E mem 8 g 96 0 0 LAY_CGIF (cgif_vals s) 51 (litsG p0 p1 p2 ih));
[exact H8 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); assumption | intros i Hi; lia].
intros j v Hj. apply (af_HX (51 + j) j v eq_refl Hj).
Qed.
Lemma af_Rg_part_ok : forall mem g p0 p1 p2 ih lo hi wlo whi,
bv_unsigned (ew E 8) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs0segs mem g LAY_CGIF (cgif_vals s) ->
pin_ok p0 (frame_ptr (nth 0 (cg_frames s) None)) -> pin_ok p1 (frame_ptr (nth 1 (cg_frames s) None)) ->
pin_ok p2 (frame_ptr (nth 2 (cg_frames s) None)) -> pin_ok ih (cg_ihead s) ->
0 <= lo -> hi <= 96 -> (forall i, wlo <= i < whi -> writable_at ubs0segs mem (g + i)) ->
region_ok ubs0segs E mem (af_Rg_part lo hi wlo whi p0 p1 p2 ih).
Proof using cf more regs0 regs1.
intros mem g p0 p1 p2 ih lo hi wlo whi H8 Hlo Hhi Hobj P0 P1 P2 Pi Hl Hh Hw. unfold af_Rg_part.
apply (region_ok_part ubs0segs E mem (Some 8%nat) 0 96 0 0); [| exact Hl | exact Hh | cbn [base_val]; rewrite H8; exact Hw].
apply (af_Rg_ok mem g p0 p1 p2 ih); assumption.
Qed.
Lemma af_Rfr_part_ok : forall mem (n : nat) p f (k : nat) lo hi wlo whi,
bv_unsigned (ew E n) = p -> p = fr_ptr f -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs0segs mem p LAY_Frame (frame_vals f) ->
(68 <= k)%nat -> (forall j v, nth_error (frame_vals f) j = Some v -> nth_error more (k - 68 + j) = Some v) ->
0 <= lo -> hi <= 40 -> (forall i, wlo <= i < whi -> writable_at ubs0segs mem (p + i)) ->
region_ok ubs0segs E mem (af_Rfr_part n k lo hi wlo whi).
Proof using cf regs0 regs1 s.
intros mem n p f k lo hi wlo whi Hn Hp Hlo Hhi Hobj Hk Hmore Hl Hh Hw. unfold af_Rfr_part.
apply (region_ok_part ubs0segs E mem (Some n) 0 40 0 0); [| exact Hl | exact Hh | cbn [base_val]; rewrite Hn; exact Hw].
eapply (region_ok_obj_gen ubs0segs E mem n p 40 0 0 LAY_Frame (frame_vals f) k []);
[exact Hn | lia | lia | exact Hobj | reflexivity | | intros [|j] z Hz; discriminate Hz | intros i Hi; lia].
intros j v Hj. apply (af_HM (k + j) (k - 68 + j) v ltac:(lia) (Hmore j v Hj)).
Qed.
End c0.
Lemma af_Rg_okE : forall E mem g s p0 p1 p2 ih,
bv_unsigned (ew E 8) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs0segs mem g LAY_CGIF (cgif_vals s) ->
(forall n j v, n = (51 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) ->
pin_ok p0 (frame_ptr (nth 0 (cg_frames s) None)) -> pin_ok p1 (frame_ptr (nth 1 (cg_frames s) None)) ->
pin_ok p2 (frame_ptr (nth 2 (cg_frames s) None)) -> pin_ok ih (cg_ihead s) ->
region_ok ubs0segs E mem (af_Rg p0 p1 p2 ih).
Proof using.
intros E mem g s p0 p1 p2 ih H8 Hlo Hhi Hobj HX P0 P1 P2 Pi. unfold af_Rg.
eapply (region_ok_obj_gen ubs0segs E mem 8 g 96 0 0 LAY_CGIF (cgif_vals s) 51 (litsG p0 p1 p2 ih));
[exact H8 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); assumption | intros i Hi; lia].
intros j v Hj. apply (HX (51 + j)%nat j v eq_refl Hj).
Qed.
Lemma af_Rg_part_okE : forall E mem g s p0 p1 p2 ih lo hi wlo whi,
bv_unsigned (ew E 8) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs0segs mem g LAY_CGIF (cgif_vals s) ->
(forall n j v, n = (51 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) ->
pin_ok p0 (frame_ptr (nth 0 (cg_frames s) None)) -> pin_ok p1 (frame_ptr (nth 1 (cg_frames s) None)) ->
pin_ok p2 (frame_ptr (nth 2 (cg_frames s) None)) -> pin_ok ih (cg_ihead s) ->
0 <= lo -> hi <= 96 -> (forall i, wlo <= i < whi -> writable_at ubs0segs mem (g + i)) ->
region_ok ubs0segs E mem (af_Rg_part lo hi wlo whi p0 p1 p2 ih).
Proof using.
intros E mem g s p0 p1 p2 ih lo hi wlo whi H8 Hlo Hhi Hobj HX P0 P1 P2 Pi Hl Hh Hw. unfold af_Rg_part.
apply (region_ok_part ubs0segs E mem (Some 8%nat) 0 96 0 0); [| exact Hl | exact Hh | cbn [base_val]; rewrite H8; exact Hw].
apply (af_Rg_okE E mem g s p0 p1 p2 ih); assumption.
Qed.
Lemma af_Rfr_part_okE : forall E mem (n : nat) p f (k : nat) lo hi wlo whi,
bv_unsigned (ew E n) = p -> p = fr_ptr f -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs0segs mem p LAY_Frame (frame_vals f) ->
(forall j v, nth_error (frame_vals f) j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
0 <= lo -> hi <= 40 -> (forall i, wlo <= i < whi -> writable_at ubs0segs mem (p + i)) ->
region_ok ubs0segs E mem (af_Rfr_part n k lo hi wlo whi).
Proof using.
intros E mem n p f k lo hi wlo whi Hn Hp Hlo Hhi Hobj HM Hl Hh Hw. unfold af_Rfr_part.
apply (region_ok_part ubs0segs E mem (Some n) 0 40 0 0); [| exact Hl | exact Hh | cbn [base_val]; rewrite Hn; exact Hw].
eapply (region_ok_obj_gen ubs0segs E mem n p 40 0 0 LAY_Frame (frame_vals f) k []);
[exact Hn | lia | lia | exact Hobj | reflexivity | exact HM | intros [|j] z Hz; discriminate Hz | intros i Hi; lia].
Qed.
Lemma HX_havoc : forall E s k ws,
(forall n j v, n = (51 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v) -> (68 <= k)%nat ->
forall n j v, n = (51 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew (havoc E k ws) n = Z_to_bv 64 v.
Proof using.
intros E s k ws HX Hk n j v Hn Hj.
assert (Hlj : (j < length (cgif_vals s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
change (length (cgif_vals s)) with 17%nat in Hlj.
rewrite ew_havoc_old by lia. exact (HX n j v Hn Hj).
Qed.
Lemma HC_havoc : forall E (cf : list Z) k ws, length cf = 7%nat ->
(forall n j v, n = (44 + j)%nat -> nth_error cf j = Some v -> ew E n = Z_to_bv 64 v) -> (51 <= k)%nat ->
forall n j v, n = (44 + j)%nat -> nth_error cf j = Some v -> ew (havoc E k ws) n = Z_to_bv 64 v.
Proof using.
intros E cf k ws Hlen HC Hk n j v Hn Hj.
assert (Hlj : (j < 7)%nat) by (rewrite <- Hlen; apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
rewrite ew_havoc_old by lia. exact (HC n j v Hn Hj).
Qed.
Lemma HK_havoc : forall E regs0 k ws,
(forall n j v, n = (32 + j)%nat -> nth_error (af_saved_vals regs0) j = Some v -> ew E n = Z_to_bv 64 v) -> (44 <= k)%nat ->
forall n j v, n = (32 + j)%nat -> nth_error (af_saved_vals regs0) j = Some v -> ew (havoc E k ws) n = Z_to_bv 64 v.
Proof using.
intros E regs0 k ws HK Hk n j v Hn Hj.
assert (Hlj : (j < length (af_saved_vals regs0))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
change (length (af_saved_vals regs0)) with 12%nat in Hlj.
rewrite ew_havoc_old by lia. exact (HK n j v Hn Hj).
Qed.
Lemma land_0_iff_bits : forall a m, 0 <= a -> 0 <= m ->
Z.land a m = 0 <-> (forall n, 0 <= n -> Z.testbit m n = true -> Z.testbit a n = false).
Proof using.
intros a m Ha Hm. split.
- intros H n Hn Hmn. apply (f_equal (fun x => Z.testbit x n)) in H. rewrite Z.land_spec, Z.bits_0, Hmn, andb_true_r in H. exact H.
- intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.testbit m n) eqn:Hmn; [rewrite (H n Hn Hmn); reflexivity | apply andb_false_r].
Qed.
Lemma land6_0 : forall a, 0 <= a -> Z.land a 6 = 0 <-> Z.land a 2 = 0 /\ Z.land a 4 = 0.
Proof using.
intros a Ha. rewrite !land_0_iff_bits by lia. split.
- intros H. split; intros n Hn Hb.
+ assert (n = 1) by (destruct (Z.eq_dec n 1) as [->|Hne]; [reflexivity|]; exfalso;
destruct (Z.eq_dec n 0) as [->|Hn0]; [cbn in Hb; discriminate|];
rewrite (Z.bits_above_log2 2 n) in Hb by (cbn; lia); discriminate). subst. apply H; [lia | reflexivity].
+ assert (n = 2) by (destruct (Z.eq_dec n 2) as [->|Hne]; [reflexivity|]; exfalso;
destruct (Z.eq_dec n 0) as [->|Hn0]; [cbn in Hb; discriminate|]; destruct (Z.eq_dec n 1) as [->|Hn1]; [cbn in Hb; discriminate|];
rewrite (Z.bits_above_log2 4 n) in Hb by (cbn; lia); discriminate). subst. apply H; [lia | reflexivity].
- intros [H2 H4] n Hn Hb.
destruct (Z.eq_dec n 1) as [->|Hn1]; [apply H2; [lia | reflexivity]|].
destruct (Z.eq_dec n 2) as [->|Hn2]; [apply H4; [lia | reflexivity]|].
exfalso. destruct (Z.eq_dec n 0) as [->|Hn0]; [cbn in Hb; discriminate|].
rewrite (Z.bits_above_log2 6 n) in Hb by (cbn; lia). discriminate.
Qed.
Lemma land_le : forall a m, 0 <= m -> 0 <= Z.land a m <= m.
Proof using. intros a m Hm. apply Z_land_upper. exact Hm. Qed.
Lemma denot_mul3 : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 1)) (SOff n 0)) = Z_to_bv 64 (3 * x).
Proof using.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n x Hn), U_SLit by lia. change (Z.land (zcanon 1) 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (x * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_mul3' : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * x).
Proof using.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 3) with 3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_add0 : forall E x, sv_denot E (SAlu ALU_ADD x (SLit 0)) = sv_denot E x.
Proof using.
intros E x. rewrite (denot_lit_U E (SAlu ALU_ADD x (SLit 0))), (denot_lit_U E x). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Lemma U_sext32_low : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) mod 2 ^ 32 = v.
Proof using.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32). apply sext32_low. exact Hv.
Qed.
Lemma U_sext16_low : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 -> U E (SExt true 16 (SOff n 0)) mod 2 ^ 16 = v.
Proof using.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 16) with (2 ^ 16). apply sext16_low. exact Hv.
Qed.
Lemma U_mulw_small : forall E a b x y,
U E a = x -> U E b = y -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 <= x * y < 2 ^ 31 ->
U E (SMdw M_MUL a b) = x * y.
Proof using.
intros E a b x y Hx Hy Rx Ry Rxy. rewrite U_of_S, S_SMdw. cbn [zmd_raw]. rewrite Hx, Hy.
rewrite !Z.mod_small by lia. rewrite swrap32_id by lia. apply wrap64_id. unfold M64. lia.
Qed.
Lemma U_zext32_shifts : forall E a x,
U E a = x -> 0 <= x < 2 ^ 32 -> U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = x.
Proof using.
intros E a x Hx Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, !U_SLit.
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 32)) by (unfold M64; change (2 ^ 32) with 4294967296 in *; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma denot_mul_atoms : forall E a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x * y < 2 ^ 64 ->
sv_denot E (SMd M_MUL (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x * y).
Proof using.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. rewrite zcanon_id by (unfold M64; nia). reflexivity.
Qed.
End h.
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Ltac af_add_region HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
