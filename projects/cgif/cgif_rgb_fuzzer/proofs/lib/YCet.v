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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCgl YCfu YCft YCrb YCez YCev YCf6 YCf2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition FB_K : nat := 210.
Definition fl_bef_region : YQ0b.region := YQ0b.mkRegion (Some 12%nat) 0 FRAME_SIZE 0 0 (obj_chunks_gen LAY_Frame 210 []).
Definition fl_bef_facts : list (nat * afact) :=
[ (12%nat, HPTR 4); (210%nat, mkAF 0 (2^64 - 1) 0); (211%nat, HPTR 4); (212%nat, mkAF 0 (2^32 - 1) 0); (213%nat, mkAF 0 (2^32 - 1) 0);
(214%nat, mkAF 0 65535 0); (215%nat, mkAF 0 65535 0); (216%nat, mkAF 0 255 0); (217%nat, mkAF 0 255 0); (218%nat, mkAF 0 255 0) ].
Definition ss_add_bef (ss : sstate) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (fl_bef_region :: ss_mem ss) (ss_resv ss)
(mkFacts (fl_bef_facts ++ f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Definition fl_Ebef (E : env) (fb : frame_st) : env := havoc E 210 (map (Z_to_bv 64) (frame_vals fb)).
Lemma atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; [exact H2|]. cbn in H1 |- *. destruct H1 as [Hf H1]. split; [exact Hf | exact (IH H1)]. Qed.
Lemma ew_Ebef_old : forall E fb n, (n < 210)%nat -> ew (fl_Ebef E fb) n = ew E n.
Proof. intros E fb n Hn. unfold fl_Ebef. apply ew_havoc_old. exact Hn. Qed.

Lemma ew_Ebef_new : forall E fb j v, nth_error (frame_vals fb) j = Some v -> ew (fl_Ebef E fb) (210 + j) = Z_to_bv 64 v.
Proof.
intros E fb j v Hj. unfold fl_Ebef.
assert (Hlt : (j < 9)%nat).
{ destruct (Nat.lt_ge_cases j 9) as [Hl|Hge]; [exact Hl|]. rewrite (proj2 (nth_error_None _ _)) in Hj; [discriminate|]. cbn [frame_vals length]. exact Hge. }
rewrite (ew_havoc_new E 210 _ j (Z_to_bv 64 0)) by (rewrite length_map; cbn [frame_vals length]; exact Hlt).
rewrite map_nth. f_equal. exact (nth_error_nth _ j 0 Hj).
Qed.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Lemma fl_bef_in : forall s i fb, (i = 1%nat \/ i = 2%nat) -> length (cg_frames s) = 3%nat ->
nth (i - 1) (cg_frames s) None = Some fb -> nth_error (cg_frames s) (i - 1) = Some (Some fb) /\ In (Some fb) (cg_frames s).
Proof.
intros s i fb Hi Hlen Hn.
assert (Hlt : (i - 1 < length (cg_frames s))%nat) by lia.
pose proof (nth_error_nth' (cg_frames s) None Hlt) as Hne. rewrite Hn in Hne.
split; [exact Hne|]. eapply nth_error_In. exact Hne.
Qed.
Lemma cgif_two_frames : forall g s N rest j1 j2 f1 f2,
nth_error (cg_frames s) j1 = Some (Some f1) -> nth_error (cg_frames s) j2 = Some (Some f2) -> j1 <> j2 ->
exists l, Permutation (cgif_blocks g s N ++ rest) ((fr_ptr f1, FRAME_SIZE) :: (fr_ptr f2, FRAME_SIZE) :: l).
Proof.
intros g s N rest j1 j2 f1 f2 H1 H2 Hne.
destruct (nth_error_split _ _ H1) as (l1 & l2 & Hfr & Hl1).
assert (Hf2 : In (Some f2) (l1 ++ l2)).
{ rewrite Hfr in H2. destruct (Nat.lt_ge_cases j2 (length l1)) as [Hlt|Hge].
- apply in_app_iff. left. rewrite nth_error_app1 in H2 by exact Hlt. eapply nth_error_In. exact H2.
- apply in_app_iff. right. rewrite nth_error_app2 in H2 by exact Hge.
destruct (j2 - length l1)%nat as [|k] eqn:Hk; [lia|]. cbn in H2. eapply nth_error_In. exact H2. }
set (tail := (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_img f1, N) :: (if Z.land (fr_attr f1) 1 =? 0 then [] else [(fr_lpal f1, 3 * fr_nlp f1)]) ++ frames_blocks N l2) ++ rest).
assert (HP : Permutation (cgif_blocks g s N ++ rest) ((fr_ptr f1, FRAME_SIZE) :: tail)).
{ unfold cgif_blocks, tail. rewrite Hfr, frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). unfold frame_blocks at 1.
apply perm_frame_front. }
assert (Hin : In (fr_ptr f2, FRAME_SIZE) tail).
{ unfold tail. right. right. apply in_app_iff. left. apply in_app_iff. right.
apply in_app_iff in Hf2 as [Hf2|Hf2].
- apply in_app_iff. left. apply af_frames_blocks_ptr_in. exact Hf2.
- apply in_app_iff. right. right. apply in_app_iff. right. apply af_frames_blocks_ptr_in. exact Hf2. }
apply in_split in Hin as (t1 & t2 & Et). exists (t1 ++ t2).
eapply Permutation_trans; [exact HP|]. apply perm_skip. rewrite Et. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma fl_bef_blocks : forall ly S g s N rest fb,
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) -> In (Some fb) (cg_frames s) ->
In (fr_ptr fb, FRAME_SIZE) (ablocks B ly S) /\ In (fr_img fb, N) (ablocks B ly S) /\
(Z.land (fr_attr fb) 1 <> 0 -> In (fr_lpal fb, 3 * fr_nlp fb) (ablocks B ly S)).
Proof.
intros ly S g s N rest fb HP Hin.
assert (Hsub : forall x, In x (frame_blocks N fb) -> In x (ablocks B ly S)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left.
unfold cgif_blocks. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some fb). split; [exact Hin | exact Hx]. }
split; [apply Hsub; left; reflexivity|]. split; [apply Hsub; right; left; reflexivity|].
intros Ha. apply Hsub. unfold frame_blocks. right. right. destruct (Z.eqb_spec (Z.land (fr_attr fb) 1) 0); [lia|]. left. reflexivity.
Qed.
Lemma fl_bef_sep : forall ly S W mem md g s N rest i f fb,
AR trbsegs B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
nth_error (cg_frames s) i = Some (Some f) -> nth_error (cg_frames s) (i - 1) = Some (Some fb) -> (i = 1%nat \/ i = 2%nat) ->
fr_ptr f + 40 <= fr_ptr fb \/ fr_ptr fb + 40 <= fr_ptr f.
Proof.
intros ly S W mem md g s N rest i f fb HAR HP Hf Hb Hi.
destruct (cgif_two_frames g s N rest i (i - 1) f fb Hf Hb ltac:(lia)) as (l & Hl).
pose proof (sep_blocks_perm trbsegs B LAWS ly S W mem md _ _ l HAR (Permutation_trans HP Hl)) as Hs.
unfold zdisjoint, block_rng in Hs. cbn [fst snd] in Hs. change (req_size FRAME_SIZE) with 40 in Hs. exact Hs.
Qed.
Lemma aj_obj_kept : forall STK sp0 FP ly S W mem md own ly' S' W' (mem' : word -> option byte) md' k p n lay vals,
ajournal trbsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
obj_at trbsegs (mrestrict (w_H W) mem) p lay vals -> lay_inside lay (req_size n) = true ->
(forall i, 0 <= i < req_size n -> ~ inFP FP (p + i)) ->
obj_at trbsegs (mrestrict (w_H W') mem') p lay vals.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n lay vals HJ Hin Hin' Hobj Hlay Hfp.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
eapply (obj_at_transport_range trbsegs); [exact Hobj | exact Hlay |].
intros i Hi. apply (mbyte_of_aview trbsegs). apply (F2 p n i Hin Hin' Hi (Hfp i Hi)).
Qed.
Lemma fl_fp_out_frame : forall (f : frame_st) (raw p : Z) i,
(p + 40 <= fr_ptr f + 20 \/ fr_ptr f + 24 <= p) -> (p + 40 <= raw + 40 \/ raw + 44 <= p) -> 0 <= i < 40 ->
~ inFP [(fr_ptr f + 20, fr_ptr f + 24); (raw + 40, raw + 44)] (p + i).
Proof.
intros f raw p i H1 H2 Hi (r & Hr & Ha). cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma st_ok_add_bef : forall E ss Hh (ms : machine_state) fb,
st_ok trbsegs E ss (restrict Hh ms) ->
ss_atoms_lt 210 ss = true ->
bv_unsigned (ew E 12) = fr_ptr fb -> 4096 <= fr_ptr fb -> fr_ptr fb + 40 <= alloc_ceiling -> fr_ptr fb mod 16 = 0 ->
4096 <= fr_img fb -> fr_img fb <= alloc_ceiling -> fr_img fb mod 16 = 0 ->
obj_at trbsegs (mrestrict Hh (ms_mem ms)) (fr_ptr fb) LAY_Frame (frame_vals fb) ->
all_disjoint (fl_Ebef E fb) fl_bef_region (ss_mem ss) ->
st_ok trbsegs (fl_Ebef E fb) (ss_add_bef ss) (restrict Hh ms).
Proof.
intros E ss Hh ms fb HS Hat H12 Hp1 Hp2 Hp16 Hi1 Hi2 Hi16 Hobj Hdisj. pose proof (proj1 asan_consts) as C1.
assert (HS1 : st_ok trbsegs (fl_Ebef E fb) ss (restrict Hh ms)).
{ eapply (st_ok_agree trbsegs 210); [exact HS | | exact Hat]. unfold fl_Ebef. apply env_agree_havoc_ge; [lia | apply env_agree_refl]. }
pose proof Hobj as Ob'. cbn [obj_at LAY_Frame LAY_FrameConfig frame_vals app] in Ob'.
destruct Ob' as ([_ Q0] & [_ Q1] & [_ Q2] & [_ Q3] & [_ Q4] & [_ Q5] & [_ Q6] & [_ Q7] & [_ Q8] & _).
cbn [fst snd N.to_nat Z.of_N] in Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8.
change (2 ^ (8 * 8)) with (2 ^ 64) in *; change (2 ^ (8 * 4)) with (2 ^ 32) in *; change (2 ^ (8 * 2)) with 65536 in *; change (2 ^ (8 * 1)) with 256 in *.
assert (EB : forall j v, nth_error (frame_vals fb) j = Some v -> ew (fl_Ebef E fb) (210 + j) = Z_to_bv 64 v) by (intros j v Hj; apply ew_Ebef_new; exact Hj).
assert (E12' : ew (fl_Ebef E fb) 12 = ew E 12) by (apply ew_Ebef_old; lia).
assert (HS2 : st_ok trbsegs (fl_Ebef E fb) (mkSS (ss_pc ss) (ss_regs ss) (fl_bef_region :: ss_mem ss) (ss_resv ss) (ss_facts ss)) (restrict Hh ms)).
{ apply (ast_ok_add_region trbsegs); [exact HS1 | vm_compute; reflexivity | | exact Hdisj].
unfold fl_bef_region. cbn [ms_mem restrict].
lazymatch goal with |- region_ok _ _ ?m _ =>
apply (region_ok_obj_gen trbsegs (fl_Ebef E fb) m 12 (fr_ptr fb) FRAME_SIZE 0 0 LAY_Frame (frame_vals fb) 210 []);
[rewrite E12'; exact H12 | lia | unfold FRAME_SIZE; lia | | vm_compute; reflexivity
| intros j v Hj; exact (EB j v Hj) | intros j z Hj; destruct j; discriminate | intros o Ho; lia] end.
destruct ms as [rg pcv m rom fr fc rv sv]. cbn [ms_mem restrict mkst] in Hobj |- *. exact Hobj. }
unfold ss_add_bef. apply (st_ok_facts trbsegs) with (ss := mkSS (ss_pc ss) (ss_regs ss) (fl_bef_region :: ss_mem ss) (ss_resv ss) (ss_facts ss)); [exact HS2|].
destruct HS2 as (_ & _ & _ & _ & _ & _ & _ & _ & [HA [HC HL]]). cbn [ss_facts] in HA, HC, HL.
split; [|split; [exact HC | exact HL]]. cbn [f_atoms]. apply atoms_ok_app; [|exact HA].
pose proof (EB 0%nat _ eq_refl) as E0. pose proof (EB 1%nat _ eq_refl) as E1. pose proof (EB 2%nat _ eq_refl) as E2.
pose proof (EB 3%nat _ eq_refl) as E3. pose proof (EB 4%nat _ eq_refl) as E4. pose proof (EB 5%nat _ eq_refl) as E5.
pose proof (EB 6%nat _ eq_refl) as E6. pose proof (EB 7%nat _ eq_refl) as E7. pose proof (EB 8%nat _ eq_refl) as E8.
cbn [Nat.add] in E0, E1, E2, E3, E4, E5, E6, E7, E8.
cbn [atoms_ok fl_bef_facts]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E12', E0, E1, E2, E3, E4, E5, E6, E7, E8, H12. rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hp1 Hp2 Hp16 Hi1 Hi2 Hi16 Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 C1. clear. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End b.
End a.
