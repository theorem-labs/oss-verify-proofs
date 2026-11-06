(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCe9 YCfx YCex YCev YCfa.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition w_trim_region (r : YQ0b.region) (lo hi : Z) : YQ0b.region :=
YQ0b.mkRegion (YQ0b.r_base r) (Z.max lo (YQ0b.r_lo r)) (Z.min hi (YQ0b.r_hi r)) (Z.max lo (YQ0b.r_wlo r)) (Z.min hi (YQ0b.r_whi r))
(List.filter (fun c => (lo <=? YQ0b.c_off c) && (YQ0b.c_off c + YQ0b.c_len c <=? hi)) (YQ0b.r_chunks r)).
Fixpoint w_trim_base (rs : smem) (n : nat) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YQ0b.r_base r with
| Some b => if Nat.eqb b n then w_trim_region r lo hi :: t else r :: w_trim_base t n lo hi
| None => r :: w_trim_base t n lo hi end end.
Lemma w_extent_disjoint_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. intros E a b [H|H]; [right | left]; exact H. Qed.
Lemma w_all_disjoint_app : forall E r l1 l2, all_disjoint E r (l1 ++ l2) <-> all_disjoint E r l1 /\ all_disjoint E r l2.
Proof.
intros E r l1 l2. induction l1 as [|x l1 IH]; cbn; [tauto|]. rewrite IH. tauto.
Qed.
Lemma w_pairwise_disjoint_remove : forall E l1 x l2, pairwise_disjoint E (l1 ++ x :: l2) -> pairwise_disjoint E (l1 ++ l2) /\ all_disjoint E x l2 /\ (forall y, In y l1 -> extent_disjoint E y x).
Proof.
intros E l1 x l2. induction l1 as [|y l1 IH]; cbn; intros H.
- destruct H as [Hx Hp]. repeat split; try assumption. intros z [].
- destruct H as [Hy Hp]. apply w_all_disjoint_app in Hy as [Hy1 [Hyx Hy2]]. destruct (IH Hp) as (P1 & P2 & P3).
split; [split; [apply w_all_disjoint_app; split; assumption | exact P1]|]. split; [exact P2|].
intros z [<- | Hz]; [exact Hyx | exact (P3 z Hz)].
Qed.
Lemma w_pairwise_disjoint_insert : forall E l1 x l2, pairwise_disjoint E (l1 ++ l2) -> all_disjoint E x (l1 ++ l2) -> pairwise_disjoint E (l1 ++ x :: l2).
Proof.
intros E l1 x l2. induction l1 as [|y l1 IH]; cbn; intros Hp Hx.
- split; [exact Hx | exact Hp].
- destruct Hp as [Hy Hp]. destruct Hx as [Hxy Hx]. apply w_all_disjoint_app in Hy as [Hy1 Hy2].
split; [apply w_all_disjoint_app; split; [exact Hy1 | cbn; split; [apply w_extent_disjoint_sym; exact Hxy | exact Hy2]] | exact (IH Hp Hx)].
Qed.
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma w_st_ok_replace_region : forall E ss ms l1 r r' l2,
st_ok trbsegs E ss ms -> ss_mem ss = l1 ++ r :: l2 ->
regions_wf (l1 ++ r' :: l2) = true -> region_ok trbsegs E (ms_mem ms) r' -> all_disjoint E r' (l1 ++ l2) ->
st_ok trbsegs E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ r' :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 r r' l2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrs Hwf' Hr' Hd.
rewrite Hrs in Hok, Hpd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb; subst. apply Forall_app. split; [exact Ha | constructor; assumption].
- destruct (w_pairwise_disjoint_remove E l1 r l2 Hpd) as (P1 & _ & _). exact (w_pairwise_disjoint_insert E l1 r' l2 P1 Hd).
Qed.
Lemma region_ok_transport_chunks : forall E E' (mem mem' : word -> option byte) n b lo hi wlo whi cs,
region_ok trbsegs E mem (YQ0b.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> ew E' n = ew E n ->
(forall c, In c cs -> match YQ0b.c_val c with CVal _ e => sv_denot E' e = sv_denot E e | CData _ _ _ => False | _ => True end) ->
(forall c, In c cs -> forall a, b + YQ0b.c_off c <= a < b + YQ0b.c_off c + YQ0b.c_len c -> mbyte trbsegs mem' a = mbyte trbsegs mem a) ->
(forall a, b + wlo <= a < b + whi -> writable_at trbsegs mem' a) ->
region_ok trbsegs E' mem' (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E E' mem mem' n b lo hi wlo whi cs HR Hb Hn Hcv Hrd Hwr. unfold region_ok in HR |- *. cbv zeta in HR |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in HR |- *.
rewrite Hn. rewrite Hb in HR |- *. destruct HR as (Hlo & Hhi & Hw & Hcs).
split; [exact Hlo|]. split; [exact Hhi|]. split; [intros o Ho; apply Hwr; lia|].
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split.
- specialize (Hcv c Hc). destruct (YQ0b.c_val c) as [w e|len|len|d s len]; cbn [cbyte] in *;
[rewrite Hcv; exact Hb1 | exact Hb1 | exact Hb1 | destruct Hcv].
- rewrite (Hrd c Hc); [exact Hb2|]. lia.
Qed.
Definition chunk_atoms_ltb (K : nat) (c : YQ0b.chunk) : bool :=
match YQ0b.c_val c with CVal _ e => sv_atoms_lt K e | CData _ _ _ => false | _ => true end.
Lemma region_ok_transport_chunksK : forall K E E' (mem mem' : word -> option byte) n b lo hi wlo whi cs,
region_ok trbsegs E mem (YQ0b.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> env_agree K E E' -> (n < K)%nat -> forallb (chunk_atoms_ltb K) cs = true ->
(forall c, In c cs -> forall a, b + YQ0b.c_off c <= a < b + YQ0b.c_off c + YQ0b.c_len c -> mbyte trbsegs mem' a = mbyte trbsegs mem a) ->
(forall a, b + wlo <= a < b + whi -> writable_at trbsegs mem' a) ->
region_ok trbsegs E' mem' (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros K E E' mem mem' n b lo hi wlo whi cs HR Hb HAG HnK Hcs Hrd Hwr.
eapply region_ok_transport_chunks; [exact HR | exact Hb | exact (proj1 HAG n HnK) | | exact Hrd | exact Hwr].
intros c Hc. pose proof (proj1 (forallb_forall _ _) Hcs c Hc) as Hcb. unfold chunk_atoms_ltb in Hcb.
destruct (YQ0b.c_val c) as [w e|len|len|d s0 len]; [apply (sv_denot_agree K); [exact HAG | exact Hcb] | exact I | exact I | discriminate Hcb].
Qed.
Definition off_scratch_free (off len : Z) : bool :=
((off + len <=? 40) || ((56 <=? off) && (off + len <=? 144)) || ((168 <=? off) && (off + len <=? 232)) || (232 <=? off))
&& (0 <=? off) && (off + len <=? 248).
Lemma off_scratch_free_sound : forall sp1 off len, off_scratch_free off len = true ->
forall a, sp1 + off <= a < sp1 + off + len -> (sp1 <= a < sp1 + 232 /\ ~ wscr sp1 a) \/ sp1 + 232 <= a < sp1 + 248.
Proof.
intros sp1 off len H a Ha. unfold off_scratch_free in H. unfold wscr.
apply andb_prop in H; destruct H as [H H280]. apply andb_prop in H; destruct H as [H H0]. apply Z.leb_le in H280. apply Z.leb_le in H0.
repeat (apply orb_prop in H; destruct H as [H|H]); try (apply andb_prop in H; destruct H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2);
try apply Z.leb_le in H; first [left; split; lia | right; lia].
Qed.
Definition chunk_scratch_freeb (c : YQ0b.chunk) : bool := off_scratch_free (YQ0b.c_off c) (YQ0b.c_len c).
Lemma perm_two_front : forall {X} (x y : X) (A Bq : list X), In y (A ++ Bq) -> exists l, Permutation (A ++ x :: Bq) (x :: y :: l).
Proof.
intros X x y A Bq Hy. apply in_split in Hy as (C & D & E). exists (C ++ D).
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite E. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma fl_frames_blocks_img_in : forall N fs f, In (Some f) fs -> In (fr_img f, N) (frames_blocks N fs).
Proof. intros N fs f H. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact H | right; left; reflexivity]. Qed.
Lemma w_gpal_block : forall (B : asyms) ly S g s N rest,
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) -> Z.land (cg_attr s) 4 = 0 -> In (cg_pal s, 3 * cg_ngp s) (ablocks B ly S).
Proof.
intros B ly S g s N rest HP Ha. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left.
unfold cgif_blocks. right. right. apply in_app_iff. left. unfold pal_blocks. rewrite (proj2 (Z.eqb_eq _ _) Ha). left. reflexivity.
Qed.
Section WL.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Lemma fl_img_sep : forall ly S W mem md g s N rest j1 j2 f1 f2,
AR trbsegs B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
nth_error (cg_frames s) j1 = Some (Some f1) -> nth_error (cg_frames s) j2 = Some (Some f2) -> j1 <> j2 ->
fr_img f1 + req_size N <= fr_img f2 \/ fr_img f2 + req_size N <= fr_img f1.
Proof.
intros ly S W mem md g s N rest j1 j2 f1 f2 HAR HP H1 H2 Hne.
destruct (nth_error_split _ _ H1) as (l1 & l2 & Hfr & Hl1).
assert (Hf2 : In (Some f2) (l1 ++ l2)).
{ rewrite Hfr in H2. destruct (Nat.lt_ge_cases j2 (length l1)) as [Hlt|Hge].
- apply in_app_iff. left. rewrite nth_error_app1 in H2 by exact Hlt. eapply nth_error_In. exact H2.
- apply in_app_iff. right. rewrite nth_error_app2 in H2 by exact Hge.
destruct (j2 - length l1)%nat as [|k] eqn:Hk; [lia|]. cbn in H2. eapply nth_error_In. exact H2. }
set (A := (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N l1 ++ [(fr_ptr f1, FRAME_SIZE)]).
set (Bq := ((if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]) ++ frames_blocks N l2) ++ rest).
assert (E1 : cgif_blocks g s N ++ rest = A ++ (fr_img f1, N) :: Bq).
{ unfold cgif_blocks, A, Bq. rewrite Hfr, frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). unfold frame_blocks at 1.
cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
assert (Hy : In (fr_img f2, N) (A ++ Bq)).
{ unfold A, Bq. apply in_app_iff in Hf2 as [Hf2|Hf2].
- apply in_app_iff. left. right. right. apply in_app_iff. right. apply in_app_iff. left. apply fl_frames_blocks_img_in. exact Hf2.
- apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. right. apply fl_frames_blocks_img_in. exact Hf2. }
destruct (perm_two_front (fr_img f1, N) (fr_img f2, N) _ _ Hy) as (l & Hl). rewrite <- E1 in Hl.
pose proof (sep_blocks_perm trbsegs B LAWS ly S W mem md _ _ l HAR (Permutation_trans HP Hl)) as Hs.
unfold zdisjoint, block_rng in Hs. cbn [fst snd] in Hs. exact Hs.
Qed.
End WL.
End h.
