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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a YI06 UI5b YI09 YI08 YI0r YI0o UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FL_MID    : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x104).
Definition FL_DIFF   : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x120).
Definition FL_DIMS   : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x764).
Definition FL_T      : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x844).
Definition FL_RAW    : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x9fc).
Definition FL_RAW2   : Z := Eval vm_compute in (ubs0_A_flushFrame + 0xa24).
Definition FL_EALLOC : Z := Eval vm_compute in (ubs0_A_flushFrame + 0xa14).
Definition FL_CALLRET: Z := Eval vm_compute in (ubs0_A_flushFrame + 0xacc).
Definition FL_RET    : Z := Eval vm_compute in (ubs0_A_flushFrame + 0xad8).
Definition FL_FRAME : Z := 272.
Lemma frame_vals_set_fr_gen : forall f v, frame_vals (set_fr_gen f v) = list_set (frame_vals f) 3 v.
Proof using. intros. reflexivity. Qed.
Lemma fr_ptr_set_fr_gen : forall f v, fr_ptr (set_fr_gen f v) = fr_ptr f. Proof using. reflexivity. Qed.
Lemma fr_img_set_fr_gen : forall f v, fr_img (set_fr_gen f v) = fr_img f. Proof using. reflexivity. Qed.
Lemma fr_attr_set_fr_gen : forall f v, fr_attr (set_fr_gen f v) = fr_attr f. Proof using. reflexivity. Qed.
Lemma fr_lpal_set_fr_gen : forall f v, fr_lpal (set_fr_gen f v) = fr_lpal f. Proof using. reflexivity. Qed.
Lemma fr_nlp_set_fr_gen : forall f v, fr_nlp (set_fr_gen f v) = fr_nlp f. Proof using. reflexivity. Qed.
Lemma frame_blocks_set_fr_gen' : forall N f v, frame_blocks N (set_fr_gen f v) = frame_blocks N f. Proof using. reflexivity. Qed.
Lemma raw_vals_flush_upd : forall g s i gen rcur, raw_vals g (flush_upd s i gen rcur) = list_set (raw_vals g s) 8 rcur.
Proof using. intros. reflexivity. Qed.
Lemma cg_raw_flush_upd : forall s i gen rcur, cg_raw (flush_upd s i gen rcur) = cg_raw s. Proof using. reflexivity. Qed.
Lemma cg_attr_flush_upd : forall s i gen rcur, cg_attr (flush_upd s i gen rcur) = cg_attr s. Proof using. reflexivity. Qed.
Lemma cg_W_flush_upd : forall s i gen rcur, cg_W (flush_upd s i gen rcur) = cg_W s. Proof using. reflexivity. Qed.
Lemma cg_H_flush_upd : forall s i gen rcur, cg_H (flush_upd s i gen rcur) = cg_H s. Proof using. reflexivity. Qed.
Lemma cg_ngp_flush_upd : forall s i gen rcur, cg_ngp (flush_upd s i gen rcur) = cg_ngp s. Proof using. reflexivity. Qed.
Lemma cg_pal_flush_upd : forall s i gen rcur, cg_pal (flush_upd s i gen rcur) = cg_pal s. Proof using. reflexivity. Qed.
Lemma rw_cur_flush_upd : forall s i gen rcur, rw_cur (flush_upd s i gen rcur) = rcur. Proof using. reflexivity. Qed.
Lemma cg_frames_flush_upd : forall s i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) ->
cg_frames (flush_upd s i gen rcur) = list_set (cg_frames s) i (Some (set_fr_gen f gen)).
Proof using.
intros s i gen rcur f H. rewrite flush_upd_wf_frames. rewrite (nth_error_nth _ _ None H). reflexivity.
Qed.
Lemma In_frames_flush_upd : forall s i gen rcur f x,
nth_error (cg_frames s) i = Some (Some f) ->
In (Some x) (cg_frames (flush_upd s i gen rcur)) -> x = set_fr_gen f gen \/ (In (Some x) (cg_frames s) /\ exists j, nth_error (cg_frames s) j = Some (Some x) /\ j <> i).
Proof using.
intros s i gen rcur f x Hf Hin. rewrite (cg_frames_flush_upd s i gen rcur f Hf) in Hin.
apply In_list_set in Hin as [H | (j & Hj & Hne)]; [left; congruence | right]. split; [eapply nth_error_In; exact Hj | exists j; auto].
Qed.
Lemma cgif_wf_flush_upd : forall s N i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) -> cgif_wf s N -> cgif_wf (flush_upd s i gen rcur) N.
Proof using.
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
Proof using.
intros g s N i gen rcur f Hf. apply flush_upd_blocks. apply (proj1 (nth_error_Some _ _)). rewrite Hf. discriminate.
Qed.
Lemma cgif_blocks_flush_upd0 : forall g s N i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) -> cgif_blocks0 g (flush_upd s i gen rcur) N = cgif_blocks0 g s N.
Proof using.
intros g s N i gen rcur f Hf. assert (Hi : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
unfold cgif_blocks0, flush_upd, pal_blocks. cbn. f_equal. f_equal. f_equal. clear Hf.
revert i Hi. generalize (cg_frames s) as l. induction l as [|o l IH]; intros [|i] Hi; cbn in *; try lia.
- destruct o as [f0|]; cbn; reflexivity.
- rewrite IH by lia. reflexivity.
Qed.
Lemma flush_upd_twice : forall s i gen rcur gen' rcur' f,
nth_error (cg_frames s) i = Some (Some f) ->
flush_upd (flush_upd s i gen rcur) i gen' rcur' = flush_upd s i gen' rcur'.
Proof using.
intros s i gen rcur gen' rcur' f Hf. unfold flush_upd at 1. cbn -[list_set].
unfold flush_upd. f_equal. rewrite (nth_error_nth _ _ None Hf). cbn [option_map].
revert i Hf. generalize (cg_frames s) as l. induction l as [|o l IH]; intros [|i] Hf; cbn in Hf |- *; try discriminate.
- injection Hf as ->. reflexivity.
- rewrite (IH i Hf). reflexivity.
Qed.
Lemma flush_upd_id : forall s i f, nth_error (cg_frames s) i = Some (Some f) -> flush_upd s i (fr_gen f) (rw_cur s) = s.
Proof using.
intros s i f Hf. unfold flush_upd. rewrite (nth_error_nth _ _ None Hf). cbn [option_map].
replace (set_fr_gen f (fr_gen f)) with f by (destruct f; reflexivity).
destruct s; cbn in *. f_equal.
revert i Hf. induction cg_frames as [|o l IH]; intros [|i] Hf; cbn in Hf |- *; try discriminate.
- injection Hf as ->. reflexivity.
- rewrite (IH i Hf). reflexivity.
Qed.
Section d.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition fl_post (regs0 : bvmap 5 word) (g : Z) (s : cgif_st) (N : Z) (i : nat) (rest FPw : list (Z * Z)) (S GPAL : list Z)
(cur : YO07.frame) (bef : option YO07.frame) (b : rbound) L A mem md (c' : config) : Prop :=
exists L' A' regs' mem' md' (r rwcur' : Z),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR FLUSH_STK (spZ regs0) FPw L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem' g (flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) rwcur') /\ cgif_wf (flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) rwcur') N /\
Permutation (blocks L' A') (cgif_blocks0 g s N ++ rest) /\
(exists code bytes, YO07.flush_frame (gcfg_of s GPAL) (rc_int (rw_cur s)) cur bef = (code, bytes) /\
Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem' md' (cg_file s) (S ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N) /\
res_ok A' (flush_rb b).
Definition fl_vals (memc : word -> option byte) (s : cgif_st) (N : Z) (f : frame_st) (bfr : option frame_st)
(GPAL : list Z) (cur : YO07.frame) (bef : option YO07.frame) : Prop :=
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs memc (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) /\
frame_relb true memc N f cur /\ oframe_relb false memc N bfr bef /\
rw_attr s = raw_attr_of (cg_attr s).
Definition fr_vblocks (N : Z) (f : frame_st) : list (Z * Z) :=
(fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]).
Definition fl_vblocks (s : cgif_st) (N : Z) (f : frame_st) (bfr : option frame_st) : list (Z * Z) :=
pal_blocks s ++ fr_vblocks N f ++ match bfr with Some b' => fr_vblocks N b' | None => [] end.
Lemma fr_vblocks_frame_blocks : forall N f x, In x (fr_vblocks N f) -> In x (frame_blocks N f).
Proof using. intros N f x Hx. unfold frame_blocks. right. exact Hx. Qed.
Lemma fl_vblocks_sub : forall g s N f bfr i,
nth_error (cg_frames s) i = Some (Some f) -> (bfr = None \/ exists j, nth_error (cg_frames s) j = Some bfr) ->
forall x, In x (fl_vblocks s N f bfr) -> In x (cgif_blocks0 g s N).
Proof using.
intros g s N f bfr i Hf Hb x Hx. unfold fl_vblocks in Hx. unfold cgif_blocks0. right. right.
apply in_app_iff in Hx as [Hx | Hx]; [apply in_app_iff; left; exact Hx | apply in_app_iff; right].
unfold frames_blocks. apply in_flat_map.
apply in_app_iff in Hx as [Hx | Hx].
- exists (Some f). split; [eapply nth_error_In; exact Hf | apply fr_vblocks_frame_blocks; exact Hx].
- destruct bfr as [b'|]; [| destruct Hx]. destruct Hb as [Hb | (j & Hj)]; [discriminate Hb|].
exists (Some b'). split; [eapply nth_error_In; exact Hj | apply fr_vblocks_frame_blocks; exact Hx].
Qed.
Lemma fl_vals_kept : forall memc memc' s N f bfr GPAL cur bef,
(forall a n k, In (a, n) (fl_vblocks s N f bfr) -> 0 <= k < n -> mbyte ubs0segs memc' (a + k) = mbyte ubs0segs memc (a + k)) ->
fl_vals memc s N f bfr GPAL cur bef -> fl_vals memc' s N f bfr GPAL cur bef.
Proof using.
intros memc memc' s N f bfr GPAL cur bef K (Hg & Hf & Hb & Hra).
assert (G8 : forall a n l, In (a, n) (fl_vblocks s N f bfr) -> garr8 ubs0segs memc a l -> Z.of_nat (length l) = n -> garr8 ubs0segs memc' a l).
{ intros a n l Hin Hl Hlen. eapply garr8_frame; [exact Hl|]. intros x Hx. replace x with (a + (x - a)) by lia. apply (K a n (x - a) Hin). lia. }
assert (FR : forall wg f' fr, (forall x, In x (fr_vblocks N f') -> In x (fl_vblocks s N f bfr)) ->
frame_relb wg memc N f' fr -> frame_relb wg memc' N f' fr).
{ intros wg f' fr Hsub (A1 & A2 & A3 & A4 & A5 & A6 & A7 & HI & HIl & HP).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [apply (G8 _ _ _ (Hsub _ ltac:(left; reflexivity)) HI HIl)|]. split; [exact HIl|].
intros H1. destruct (HP H1) as [HLP HLPl]. split; [|exact HLPl].
apply (G8 (fr_lpal f') (3 * fr_nlp f') _ ltac:(apply Hsub; unfold fr_vblocks; right; destruct (Z.eqb_spec (Z.land (fr_attr f') 1) 0); [lia|]; left; reflexivity) HLP).
rewrite HLPl. lia. }
split; [|split; [|split; [|exact Hra]]].
- intros Hz. destruct (Hg Hz) as [HG HGl]. split; [|exact HGl]. apply (G8 (cg_pal s) (3 * cg_ngp s) GPAL); [|exact HG|exact HGl].
unfold fl_vblocks, pal_blocks. rewrite (proj2 (Z.eqb_eq _ _) Hz). left. reflexivity.
- apply (FR true f cur); [|exact Hf]. intros x Hx. unfold fl_vblocks. apply in_app_iff. right. apply in_app_iff. left. exact Hx.
- destruct bfr as [b'|]; destruct bef as [fr|]; cbn [oframe_relb] in Hb |- *; try exact Hb.
apply (FR false b' fr); [|exact Hb]. intros x Hx. unfold fl_vblocks. apply in_app_iff. right. apply in_app_iff. right. exact Hx.
Qed.
Lemma flag_raw_attr_of : forall a, YO07.flag (raw_attr_of a) 1 = YO07.flag a 2.
Proof using.
intros a. unfold raw_attr_of, YO07.flag.
destruct (Z.land a 2 =? 0), (Z.land a 16 =? 0); reflexivity.
Qed.
Lemma raw_sgct_model : forall s GPAL, raw_sgct s = (if YO07.flag (YO07.g_attr (gcfg_of s GPAL)) 4 then 0 else YO07.g_ngp (gcfg_of s GPAL)).
Proof using. intros s GPAL. unfold raw_sgct, YO07.flag. cbn. destruct (Z.land (cg_attr s) 4 =? 0); reflexivity. Qed.
Definition fl_sink (g : Z) (s : cgif_st) (N : Z) (rest FP FPw : list (Z * Z)) (S : list Z)
(L : layout) (A : astate) (mem : word -> option byte) (md : Model) (sp0 : Z) : Prop :=
sink_at ubs0_msyms mem md (cg_file s) S /\ Z.of_nat (length S) + FRAME_OUT N <= SINK_MAX /\ sp0 <= 2 ^ 47 /\
In (cg_file s, FILE_BLOCK) (blocks L A) /\ In (cg_file s, FILE_BLOCK) rest /\
~ sink_open_fp FP /\ fp_avoids FP (cg_file s) (cg_file s + FILE_BLOCK) /\
(forall a, inFP FP a -> inFP FPw a) /\ (forall a, inFP (sink_fp (cg_file s)) a -> inFP FPw a).
Definition fl_fp (FP : list (Z * Z)) (s : cgif_st) (f : frame_st) : Prop :=
(forall a, cg_raw s + 40 <= a < cg_raw s + 44 -> inFP FP a) /\ (forall a, fr_ptr f + 20 <= a < fr_ptr f + 24 -> inFP FP a).
Lemma journal_fp_weaken : forall STK sp0 FP FP' L A mem md L' A' mem' md',
(forall a, inFP FP a -> inFP FP' a) ->
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' -> journal ubs0_msyms MR STK sp0 FP' L A mem md L' A' mem' md'.
Proof using API.
intros STK sp0 FP FP' L A mem md L' A' mem' md' HI (HH & Hos & Hhi & Hblk & Hgone & Hst & Herr & Himg).
assert (HO : sink_open_fp FP -> sink_open_fp FP') by (intros Ho; exact (HI 0 Ho)).
split; [exact HH|]. split; [exact (os_step_mono _ _ _ _ HO Hos)|].
split; [exact Hhi|]. split; [intros a n i H1 H2 Hi Hn; exact (Hblk a n i H1 H2 Hi (fun Hx => Hn (HI _ Hx)))|].
split; [intros a n i H1 H2 Hi; exact (HI _ (Hgone a n i H1 H2 Hi))|].
split; [exact Hst|]. split; [exact Herr|]. eapply img_kept_mono; [exact HO | exact Himg].
Qed.
End d.
Section e.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Lemma cgif_at_low0 : forall m m' g s N Lc Ac memc mdc rest,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ rest) ->
cgif_at m g s -> (forall a, 0 <= a < alloc_ceiling -> mbyte ubs0segs m' a = mbyte ubs0segs m a) -> cgif_at m' g s.
Proof using LAWS.
intros m m' g s N Lc Ac memc mdc rest HH HB (Hg & Hr & Hf) Hlow.
assert (R : forall b n, In (b, n) (cgif_blocks0 g s N) -> 4096 <= b /\ b + n <= alloc_ceiling).
{ intros b n Hin. eapply (blocks_range _ _ LAWS); [exact HH|]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hin. }
unfold cgif_blocks0 in R.
split; [|split].
- destruct (R g CGIF_SIZE ltac:(left; reflexivity)) as [R1 R2]. unfold CGIF_SIZE in R2.
eapply obj_at_transport_range; [exact Hg | exact (proj1 LAY_CGIF_ok) |]. intros i Hi. unfold CGIF_SIZE in Hi. apply Hlow. lia.
- destruct (R (cg_raw s) RAW_SIZE ltac:(right; left; reflexivity)) as [R1 R2]. unfold RAW_SIZE in R2.
eapply obj_at_transport_range; [exact Hr | exact (proj1 LAY_Raw_ok) |]. intros i Hi. unfold RAW_SIZE in Hi. apply Hlow. lia.
- intros f Hin.
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (cgif_blocks0 g s N)).
{ unfold cgif_blocks0. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin|]. left. reflexivity. }
destruct (R (fr_ptr f) FRAME_SIZE Hfb) as [R1 R2]. unfold FRAME_SIZE in R2.
eapply obj_at_transport_range; [exact (Hf f Hin) | exact (proj1 LAY_Frame_ok) |]. intros i Hi. unfold FRAME_SIZE in Hi. apply Hlow. lia.
Qed.
Lemma cgif_at_kept0 : forall m m' g s N (bl rest : list (Z * Z)),
Permutation bl (cgif_blocks0 g s N ++ rest) ->
cgif_at m g s -> (forall b n i, In (b, n) bl -> 0 <= i < n -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m (b + i)) ->
cgif_at m' g s.
Proof using.
intros m m' g s N bl rest HB (Hg & Hr & Hf) Hkeep.
assert (K : forall b n, In (b, n) (cgif_blocks0 g s N) -> forall i, 0 <= i < n -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m (b + i)).
{ intros b n Hin i Hi. apply (Hkeep b n i); [|exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. exact Hin. }
unfold cgif_blocks0 in K.
split; [|split].
- eapply obj_at_transport_range; [exact Hg | exact (proj1 LAY_CGIF_ok) |]. apply (K g CGIF_SIZE). left. reflexivity.
- eapply obj_at_transport_range; [exact Hr | exact (proj1 LAY_Raw_ok) |]. apply (K (cg_raw s) RAW_SIZE). right. left. reflexivity.
- intros f Hin. eapply obj_at_transport_range; [exact (Hf f Hin) | exact (proj1 LAY_Frame_ok) |]. apply (K (fr_ptr f) FRAME_SIZE).
right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
Qed.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma jfree_tmp_sinkW :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
In (a, n) (blocks Lc Ac) -> (In (a, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (a + i)) ->
In (f, FILE_BLOCK) (blocks Lc Ac) -> (a + n <= f \/ f + FILE_BLOCK <= a) ->
sink_at ubs0_msyms (ms_mem ms) mdc f S ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S HS Hpc Hrv HJ Hid Hin Hnew Hfin Hsep HSK H10 H2 Hspc Hal Hlo Hhi H4 H1 Hraw.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [(a, a + n)] HJ) as HJl.
destruct (blocks_range _ _ LAWS Lc Ac (ms_mem ms) mdc a n (proj1 HJ) Hin) as [Ha0 Ha1].
eapply SR_mono.
{ eapply (jfree_at _ _ LAWS ubs0_errno_low IMG (aa_free API)) with (a := a) (n := n) (spc := spc);
[ exact HS | exact Hpc | exact Hrv | exact HJl | exact Hin | exact H10 | exact H2 | exact Hspc | exact Hal | exact Hlo | exact Hhi | exact H4 | exact H1 | exact Hraw | ].
intros _ i Hi. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2).
assert (HK : sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJ2 | | exact Hfin | | exact HSK].
- intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
- intros x Hx (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ | exact HJ2 | lia | lia |].
intros x (r & [<- | []] & Hr). cbn [fst snd] in Hr.
destruct (in_dec (fun p q : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (a, n) (blocks L A)) as [HinA | HninA].
- left. split; [| lia]. replace x with (a + (x - a)) by lia. apply (Hnew HinA). lia.
- right. exists a, n. split; [exact Hin|]. split; [exact HninA | lia]. }
split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hrm|]. split; [exact Hkeep|]. split; [exact Hhi2 | exact HK].
Qed.
Lemma fl_file_sep : forall L A m md g s N (X rest : list (Z * Z)) bb nn,
heap_ok MR L A m md -> Permutation (blocks L A) (X ++ cgif_blocks0 g s N ++ rest) -> In (cg_file s, FILE_BLOCK) rest ->
In (bb, nn) (cgif_blocks0 g s N) -> cg_file s + FILE_BLOCK <= bb \/ bb + nn <= cg_file s.
Proof using LAWS.
intros L A m md g s N X rest bb nn HH HB Hf Hin.
destruct (in_split _ _ Hf) as (r1 & r2 & Hr).
assert (HBf : Permutation (blocks L A) ((cg_file s, FILE_BLOCK) :: X ++ cgif_blocks0 g s N ++ r1 ++ r2)).
{ eapply Permutation_trans; [exact HB|]. rewrite Hr.
change (X ++ cgif_blocks0 g s N ++ r1 ++ (cg_file s, FILE_BLOCK) :: r2) with ((X ++ cgif_blocks0 g s N ++ r1) ++ (cg_file s, FILE_BLOCK) :: r2) at 1 || rewrite !app_assoc.
replace (X ++ cgif_blocks0 g s N ++ r1 ++ (cg_file s, FILE_BLOCK) :: r2) with ((X ++ cgif_blocks0 g s N ++ r1) ++ (cg_file s, FILE_BLOCK) :: r2) by (rewrite <- !app_assoc; reflexivity).
replace ((cg_file s, FILE_BLOCK) :: X ++ cgif_blocks0 g s N ++ r1 ++ r2) with ((cg_file s, FILE_BLOCK) :: (X ++ cgif_blocks0 g s N ++ r1) ++ r2) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_sym. apply Permutation_middle. }
pose proof (heap_sep_perm _ _ LAWS L A m md (cg_file s, FILE_BLOCK) _ (bb, nn) HH HBf) as Hs. cbn [fst snd] in Hs. apply Hs.
apply in_app_iff. right. apply in_app_iff. left. exact Hin.
Qed.
Lemma jfree_tmp_sinkW_res :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S (b : rbound),
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
In (a, n) (blocks Lc Ac) -> (In (a, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (a + i)) ->
In (f, FILE_BLOCK) (blocks Lc Ac) -> (a + n <= f \/ f + FILE_BLOCK <= a) ->
sink_at ubs0_msyms (ms_mem ms) mdc f S ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
res_ok Ac b ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2) /\
st_init_done A2 = true /\ res_ok A2 (rb_free b n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S b HS Hpc Hrv HJ Hid Hin Hnew Hfin Hsep HSK H10 H2 Hspc Hal Hlo Hhi H4 H1 Hraw HRb.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [(a, a + n)] HJ) as HJl.
destruct (blocks_range _ _ LAWS Lc Ac (ms_mem ms) mdc a n (proj1 HJ) Hin) as [Ha0 Ha1].
eapply SR_mono.
{ eapply (jfree_at_res API IMG) with (a := a) (n := n) (spc := spc);
[ exact HS | exact Hpc | exact Hrv | exact HJl | exact Hin | exact HRb | exact H10 | exact H2 | exact Hspc | exact Hal | exact Hlo | exact Hhi | exact H4 | exact H1 | exact Hraw | ].
intros _ i Hi. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2 & HR2).
assert (HK : sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJ2 | | exact Hfin | | exact HSK].
- intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
- intros x Hx (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ | exact HJ2 | lia | lia |].
intros x (r & [<- | []] & Hr). cbn [fst snd] in Hr.
destruct (in_dec (fun p q : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (a, n) (blocks L A)) as [HinA | HninA].
- left. split; [| lia]. replace x with (a + (x - a)) by lia. apply (Hnew HinA). lia.
- right. exists a, n. split; [exact Hin|]. split; [exact HninA | lia]. }
split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hrm|]. split; [exact Hkeep|]. split; [exact Hhi2|]. split; [exact (proj1 HK)|]. split; [exact (proj2 HK)|]. split; [exact Hid2 | exact HR2].
Qed.
End e.
Definition FL_SAVED : list reg := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition fl_saved_vals (regs0 : bvmap 5 word) : list Z := map (fun r : reg => bv_unsigned (getr regs0 r)) FL_SAVED.
Definition fl_saved_ok (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j (r : reg), nth_error FL_SAVED j = Some r -> word_mem ubs0segs mem (sp0 - 8 - 8 * Z.of_nat j) (bv_unsigned (getr regs0 r)).
Definition fl_stk_saved (k : nat) : list YP09.chunk :=
map (fun j => mkChunk (264 - 8 * Z.of_nat j) (CVal 8 (SOff (k + j) 0))) (seq 0 13).
Definition fl_untouched (regs0 regs1 : bvmap 5 word) : Prop :=
getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4.
Lemma fl_saved_vals_nth : forall regs0 j r,
nth_error FL_SAVED j = Some r -> nth_error (fl_saved_vals regs0) j = Some (bv_unsigned (getr regs0 r)).
Proof using. intros regs0 j r H. unfold fl_saved_vals. rewrite nth_error_map, H. reflexivity. Qed.
Lemma fl_saved_ok_kept : forall m m' sp0 regs0,
fl_saved_ok m sp0 regs0 -> (forall a, sp0 - 104 <= a < sp0 -> mbyte ubs0segs m' a = mbyte ubs0segs m a) -> fl_saved_ok m' sp0 regs0.
Proof using.
intros m m' sp0 regs0 H Hf j r Hr k Hk.
assert (Hj : (j < 13)%nat) by (apply (proj1 (nth_error_Some FL_SAVED j)); rewrite Hr; discriminate).
rewrite Hf by lia. apply (H j r Hr). exact Hk.
Qed.
Lemma fl_saved_chunks_ok : forall E mem sp0 regs0 k,
fl_saved_ok mem sp0 regs0 ->
(forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
Forall (chunk_ok ubs0segs E mem (sp0 - 272)) (fl_stk_saved k).
Proof using.
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
Lemma fl_saved_of_chunks : forall E mem sp0 regs0 k cs,
Forall (chunk_ok ubs0segs E mem (sp0 - 272)) cs ->
incl (fl_stk_saved k) cs ->
(forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
fl_saved_ok mem sp0 regs0.
Proof using.
intros E mem sp0 regs0 k cs Hcs Hincl HK j r Hr.
assert (Hj : (j < 13)%nat) by (apply (proj1 (nth_error_Some FL_SAVED j)); rewrite Hr; discriminate).
pose proof (proj1 (Forall_forall _ _) Hcs (mkChunk (264 - 8 * Z.of_nat j) (CVal 8 (SOff (k + j) 0)))
ltac:(apply Hincl; unfold fl_stk_saved; apply in_map_iff; exists j; split; [reflexivity | apply in_seq; lia])) as Hc.
apply val_mem_word_mem. replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 - 272 + (264 - 8 * Z.of_nat j)) by lia.
eapply (val_of_chunk_ok ubs0segs E mem (sp0 - 272) _ 8%N); [exact Hc | | cbn; apply u64_range_getr | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, (HK j _ (fl_saved_vals_nth regs0 j r Hr)), Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition A_K : nat := 32.
Definition A_X : nat := 45.
Definition A_F : nat := 62.
Definition A_B : nat := 71.
Definition A_Mo : nat := 80.
Definition fb_vals (fb : option frame_st) : list Z :=
match fb with Some b => frame_vals b | None => [0; 0; 0; 0; 0; 0; 0; 0; 0] end.
Lemma fb_vals_length : forall fb, length (fb_vals fb) = 9%nat.
Proof using. intros [b|]; reflexivity. Qed.
Definition fl_AL (regs0 : bvmap 5 word) (s : cgif_st) (f : frame_st) (fb : option frame_st) (more : list Z) : list Z :=
fl_saved_vals regs0 ++ cgif_vals s ++ frame_vals f ++ fb_vals fb ++ more.
Definition fl_E (regs1 regs0 : bvmap 5 word) (s : cgif_st) (f : frame_st) (fb : option frame_st) (more : list Z) : env :=
Ereg regs1 (map (Z_to_bv 64) (fl_AL regs0 s f fb more) ++ []).
Definition fl_litsG : list (option Z) := litsG None None None None.
Definition fl_Rg : YP09.region := YP09.mkRegion (Some 8%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG).
Definition fl_Rg_part (lo hi : Z) : YP09.region :=
YP09.mkRegion (Some 8%nat) lo hi 0 0 (chunks_between lo hi (obj_chunks_gen LAY_CGIF A_X fl_litsG)).
Definition fl_Rf (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 9%nat) 0 40 wlo whi (obj_chunks_gen LAY_Frame A_F []).
Definition fl_Rf_part (lo hi wlo whi : Z) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo hi wlo whi (chunks_between lo hi (obj_chunks_gen LAY_Frame A_F [])).
Definition fl_Rfb (n : nat) : YP09.region := YP09.mkRegion (Some n) 0 40 0 0 (obj_chunks_gen LAY_Frame A_B []).
Definition fl_Rfb_part (n : nat) (lo hi : Z) : YP09.region :=
YP09.mkRegion (Some n) lo hi 0 0 (chunks_between lo hi (obj_chunks_gen LAY_Frame A_B [])).
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
Section h.
Variables (regs1 regs0 : bvmap 5 word) (s : cgif_st) (f : frame_st) (fb : option frame_st) (more : list Z).
Let E := fl_E regs1 regs0 s f fb more.
Lemma fl_HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr.
Proof using f fb more regs0 s. intros n rr H. unfold E, fl_E. apply ew_Ereg_nat. exact H. Qed.
Lemma fl_HA : forall j v, nth_error (fl_AL regs0 s f fb more) j = Some v -> ew E (32 + j) = Z_to_bv 64 v.
Proof using regs1. intros j v H. unfold E, fl_E. apply Ereg_vals. exact H. Qed.
Lemma fl_HK : forall n j v, n = (32 + j)%nat -> nth_error (fl_saved_vals regs0) j = Some v -> ew E n = Z_to_bv 64 v.
Proof using f fb more regs1 s.
intros n j v -> H. apply fl_HA. unfold fl_AL. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma fl_HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error FL_SAVED j = Some r -> ew E n = getr regs0 r.
Proof using f fb more regs1 s. intros n j r Hn Hr. rewrite (fl_HK n j _ Hn (fl_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. Qed.
Lemma fl_HX : forall n j v, n = (45 + j)%nat -> nth_error (cgif_vals s) j = Some v -> ew E n = Z_to_bv 64 v.
Proof using f fb more regs0 regs1.
intros n j v -> H. replace (45 + j)%nat with (32 + (length (fl_saved_vals regs0) + j))%nat by reflexivity.
apply fl_HA. unfold fl_AL. rewrite nth_error_app_len. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma fl_HF : forall n j v, n = (62 + j)%nat -> nth_error (frame_vals f) j = Some v -> ew E n = Z_to_bv 64 v.
Proof using fb more regs0 regs1 s.
intros n j v -> H. replace (62 + j)%nat with (32 + (length (fl_saved_vals regs0 ++ cgif_vals s) + j))%nat by reflexivity.
apply fl_HA. unfold fl_AL. rewrite app_assoc, nth_error_app_len. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma fl_HB : forall n j v, n = (71 + j)%nat -> nth_error (fb_vals fb) j = Some v -> ew E n = Z_to_bv 64 v.
Proof using f more regs0 regs1 s.
intros n j v -> H. replace (71 + j)%nat with (32 + (length (fl_saved_vals regs0 ++ cgif_vals s ++ frame_vals f) + j))%nat by (rewrite !length_app; reflexivity).
apply fl_HA. unfold fl_AL. rewrite 2!app_assoc, nth_error_app_len. rewrite nth_error_app1; [exact H|].
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma fl_HM : forall n j v, n = (80 + j)%nat -> nth_error more j = Some v -> ew E n = Z_to_bv 64 v.
Proof using f fb regs0 regs1 s.
intros n j v -> H.
replace (80 + j)%nat with (32 + (length (fl_saved_vals regs0 ++ cgif_vals s ++ frame_vals f ++ fb_vals fb) + j))%nat
by (rewrite !length_app, fb_vals_length; reflexivity).
apply fl_HA. unfold fl_AL. rewrite 3!app_assoc, nth_error_app_len. exact H.
Qed.
Lemma fl_Rg_ok : forall mem g,
bv_unsigned (ew E 8) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs0segs mem g LAY_CGIF (cgif_vals s) -> region_ok ubs0segs E mem fl_Rg.
Proof using f fb more regs0 regs1.
intros mem g H8 Hlo Hhi Hobj. unfold fl_Rg, fl_litsG, A_X.
eapply (region_ok_obj_gen ubs0segs E mem 8 g 96 0 0 LAY_CGIF (cgif_vals s) 45 (litsG None None None None));
[exact H8 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros i Hi; lia].
intros j v Hj. apply (fl_HX (45 + j) j v eq_refl Hj).
Qed.
Lemma fl_Rg_part_ok : forall mem g lo hi,
bv_unsigned (ew E 8) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs0segs mem g LAY_CGIF (cgif_vals s) -> 0 <= lo -> hi <= 96 ->
region_ok ubs0segs E mem (fl_Rg_part lo hi).
Proof using f fb more regs0 regs1.
intros mem g lo hi H8 Hlo Hhi Hobj Hl Hh. unfold fl_Rg_part.
apply (region_ok_part ubs0segs E mem (Some 8%nat) 0 96 0 0); [| exact Hl | exact Hh | intros i Hi; lia].
apply (fl_Rg_ok mem g); assumption.
Qed.
Lemma fl_Rf_ok : forall mem p wlo whi,
bv_unsigned (ew E 9) = p -> p = fr_ptr f -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs0segs mem p LAY_Frame (frame_vals f) ->
(forall i, wlo <= i < whi -> writable_at ubs0segs mem (p + i)) ->
region_ok ubs0segs E mem (fl_Rf wlo whi).
Proof using fb more regs0 regs1 s.
intros mem p wlo whi H9 Hp Hlo Hhi Hobj Hw. unfold fl_Rf, A_F.
eapply (region_ok_obj_gen ubs0segs E mem 9 p 40 wlo whi LAY_Frame (frame_vals f) 62 []);
[exact H9 | lia | lia | exact Hobj | reflexivity | | intros [|j] z Hz; discriminate Hz | exact Hw].
intros j v Hj. apply (fl_HF (62 + j) j v eq_refl Hj).
Qed.
Lemma fl_Rf_part_ok : forall mem p lo hi wlo whi,
bv_unsigned (ew E 9) = p -> p = fr_ptr f -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs0segs mem p LAY_Frame (frame_vals f) -> 0 <= lo -> hi <= 40 ->
(forall i, wlo <= i < whi -> writable_at ubs0segs mem (p + i)) ->
region_ok ubs0segs E mem (fl_Rf_part lo hi wlo whi).
Proof using fb more regs0 regs1 s.
intros mem p lo hi wlo whi H9 Hp Hlo Hhi Hobj Hl Hh Hw. unfold fl_Rf_part.
apply (region_ok_part ubs0segs E mem (Some 9%nat) 0 40 wlo whi); [| exact Hl | exact Hh | cbn [base_val]; rewrite H9; exact Hw].
apply (fl_Rf_ok mem p); assumption.
Qed.
Lemma fl_Rfb_ok : forall mem (n : nat) p b,
bv_unsigned (ew E n) = p -> fb = Some b -> p = fr_ptr b -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs0segs mem p LAY_Frame (frame_vals b) ->
region_ok ubs0segs E mem (fl_Rfb n).
Proof using f more regs0 regs1 s.
intros mem n p b Hn Hfb Hp Hlo Hhi Hobj. unfold fl_Rfb, A_B.
eapply (region_ok_obj_gen ubs0segs E mem n p 40 0 0 LAY_Frame (frame_vals b) 71 []);
[exact Hn | lia | lia | exact Hobj | reflexivity | | intros [|j] z Hz; discriminate Hz | intros i Hi; lia].
intros j v Hj. apply (fl_HB (71 + j) j v eq_refl). rewrite Hfb. exact Hj.
Qed.
Lemma fl_Rfb_part_ok : forall mem (n : nat) p b lo hi,
bv_unsigned (ew E n) = p -> fb = Some b -> p = fr_ptr b -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs0segs mem p LAY_Frame (frame_vals b) -> 0 <= lo -> hi <= 40 ->
region_ok ubs0segs E mem (fl_Rfb_part n lo hi).
Proof using f more regs0 regs1 s.
intros mem n p b lo hi Hn Hfb Hp Hlo Hhi Hobj Hl Hh. unfold fl_Rfb_part.
apply (region_ok_part ubs0segs E mem (Some n) 0 40 0 0); [| exact Hl | exact Hh | intros i Hi; lia].
apply (fl_Rfb_ok mem n p b); assumption.
Qed.
Lemma fl_gfacts_ok : forall mem g N, obj_at ubs0segs mem g LAY_CGIF (cgif_vals s) -> cgif_wf s N ->
4096 <= cg_raw s -> cg_raw s <= alloc_ceiling -> atoms_ok E fl_gfacts.
Proof using f fb more regs0 regs1.
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
Lemma fl_ffacts_ok : forall mem p, obj_at ubs0segs mem p LAY_Frame (frame_vals f) ->
4096 <= fr_img f -> fr_img f <= alloc_ceiling -> atoms_ok E fl_ffacts.
Proof using fb more regs0 regs1 s.
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
Lemma fl_bfacts_ok : forall mem p b, fb = Some b -> obj_at ubs0segs mem p LAY_Frame (frame_vals b) ->
4096 <= fr_img b -> fr_img b <= alloc_ceiling -> atoms_ok E fl_bfacts.
Proof using f more regs0 regs1 s.
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
End h.
Section t.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Definition fl_inv (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (gen1 : Z) (rest : list (Z * Z)) (tmp : list (Z * Z)) : Prop :=
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\
(i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks g s N ++ rest).
Lemma fl_img_geom : forall L A m md g s N rest f,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks g s N ++ rest) -> In (Some f) (cg_frames s) -> 1 <= N ->
4096 <= fr_img f /\ fr_img f + N <= alloc_ceiling.
Proof using LAWS.
intros L A m md g s N rest f HH HB Hin HN.
destruct (af_frame_geom API L A m md g s N rest f HH HB Hin) as (_ & Himg & _).
exact (blocks_range _ _ LAWS L A m md (fr_img f) N HH Himg).
Qed.
Lemma fl_img_geom0 : forall L A m md g s N rest f,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) -> In (Some f) (cg_frames s) -> 1 <= N ->
4096 <= fr_img f /\ fr_img f + N <= alloc_ceiling.
Proof using LAWS.
intros L A m md g s N rest f HH HB Hin HN.
destruct (af_frame_geom0 API L A m md g s N rest f HH HB Hin) as (_ & Himg & _).
exact (blocks_range _ _ LAWS L A m md (fr_img f) N HH Himg).
Qed.
End t.
Lemma perm_img_front : forall {X} (g r x i : X) (pal F1 pf F2 rest : list X),
Permutation (g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest) (r :: g :: i :: (pal ++ F1 ++ x :: pf ++ F2) ++ rest).
Proof using.
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
Proof using.
intros g s N rest i f Hf.
destruct (nth_error_split _ _ Hf) as (l1 & l2 & Hfr & Hl1).
exists ((((cg_file s, FILE_BLOCK) :: pal_blocks s) ++ frames_blocks N l1 ++ (fr_ptr f, FRAME_SIZE) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) ++ frames_blocks N l2) ++ rest).
split.
- unfold cgif_blocks. rewrite Hfr, frames_blocks_app, frames_blocks_cons_some. unfold frame_blocks at 1.
cbn [app]. apply (perm_img_front _ _ _ _ ((cg_file s, FILE_BLOCK) :: pal_blocks s)).
- intros Ha. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. right.
apply in_app_iff. left. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
Lemma flush_blocks_img00 : forall g s N rest i f, nth_error (cg_frames s) i = Some (Some f) ->
exists rest0, Permutation (cgif_blocks0 g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (fr_img f, N) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0) /\ (forall x, In x rest -> In x rest0).
Proof using.
intros g s N rest i f Hf.
destruct (nth_error_split _ _ Hf) as (l1 & l2 & Hfr & Hl1).
exists ((pal_blocks s ++ frames_blocks N l1 ++ (fr_ptr f, FRAME_SIZE) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) ++ frames_blocks N l2) ++ rest).
split; [| split].
- unfold cgif_blocks0. rewrite Hfr, frames_blocks_app, frames_blocks_cons_some. unfold frame_blocks at 1.
cbn [app]. apply perm_img_front.
- intros Ha. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. right.
apply in_app_iff. left. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
- intros x Hx. apply in_app_iff. right. exact Hx.
Qed.
Lemma flush_blocks_img1 : forall g s N rest f p Nt, In (Some f) (cg_frames s) ->
exists rest0, Permutation ((p, Nt) :: cgif_blocks g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (p, Nt) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0).
Proof using.
intros g s N rest f p Nt Hf.
exists ((((cg_file s, FILE_BLOCK) :: pal_blocks s) ++ frames_blocks N (cg_frames s)) ++ rest). split.
- unfold cgif_blocks. cbn [app].
eapply Permutation_trans; [apply perm_skip; apply perm_swap|].
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
- intros Ha. apply in_app_iff. left. apply in_app_iff. right.
unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hf|].
unfold frame_blocks. right. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
Lemma flush_blocks_img10 : forall g s N rest f p Nt, In (Some f) (cg_frames s) ->
exists rest0, Permutation ((p, Nt) :: cgif_blocks0 g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (p, Nt) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0) /\ (forall x, In x rest -> In x rest0).
Proof using.
intros g s N rest f p Nt Hf.
exists ((pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest). split; [| split].
- unfold cgif_blocks0. cbn [app].
eapply Permutation_trans; [apply perm_skip; apply perm_swap|].
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
- intros Ha. apply in_app_iff. left. apply in_app_iff. right.
unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hf|].
unfold frame_blocks. right. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
- intros x Hx. apply in_app_iff. right. exact Hx.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
