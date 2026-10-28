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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_chunk_lowv : forall E ss ms i rg p off (n : N) e a (k : nat) (m : Z),
st_ok ubs0segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) -> bv_unsigned (ew E p) = a -> Z.of_N n <= 8 ->
k = N.to_nat n -> m = 2 ^ (8 * Z.of_N n) ->
val_mem ubs0segs (ms_mem ms) (a + off) k (U E e mod m).
Proof using.
intros E ss ms i rg p off n e a k m HS Hi Hb Hin Hp Hn -> ->.
pose proof (st_region_chunks ubs0segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
unfold U. exact (val_mem_low_of_chunk ubs0segs E (ms_mem ms) a off n e Hc Hn).
Qed.
Definition rewin (rg : YP09.region) (wlo whi : Z) : YP09.region :=
YP09.mkRegion (r_base rg) (r_lo rg) (r_hi rg) wlo whi (r_chunks rg).
Lemma extent_disjoint_rewin_l : forall E rg wlo whi r, extent_disjoint E (rewin rg wlo whi) r <-> extent_disjoint E rg r.
Proof using. intros. unfold extent_disjoint, rewin. cbn. tauto. Qed.
Lemma extent_disjoint_rewin_r : forall E rg wlo whi r, extent_disjoint E r (rewin rg wlo whi) <-> extent_disjoint E r rg.
Proof using. intros. unfold extent_disjoint, rewin. cbn. tauto. Qed.
Lemma all_disjoint_rewin_hd : forall E rg wlo whi rs, all_disjoint E rg rs -> all_disjoint E (rewin rg wlo whi) rs.
Proof using. intros E rg wlo whi rs. induction rs as [|r rs IH]; cbn; [tauto|]. intros [H1 H2]. split; [apply (proj2 (extent_disjoint_rewin_l _ _ _ _ _)); exact H1 | exact (IH H2)]. Qed.
Lemma all_disjoint_set : forall E r rs i rg wlo whi, all_disjoint E r rs -> nth_error rs i = Some rg -> all_disjoint E r (list_set rs i (rewin rg wlo whi)).
Proof using.
intros E r rs. induction rs as [|r' rs IH]; intros [|i] rg wlo whi H Hi; cbn in Hi |- *; try discriminate Hi.
- injection Hi as ->. destruct H as [H1 H2]. split; [apply (proj2 (extent_disjoint_rewin_r _ _ _ _ _)); exact H1 | exact H2].
- destruct H as [H1 H2]. split; [exact H1 | exact (IH i rg wlo whi H2 Hi)].
Qed.
Lemma pairwise_disjoint_set : forall E rs i rg wlo whi, pairwise_disjoint E rs -> nth_error rs i = Some rg -> pairwise_disjoint E (list_set rs i (rewin rg wlo whi)).
Proof using.
intros E rs. induction rs as [|r rs IH]; intros [|i] rg wlo whi H Hi; cbn in Hi |- *; try discriminate Hi.
- injection Hi as ->. destruct H as [H1 H2]. split; [apply all_disjoint_rewin_hd; exact H1 | exact H2].
- destruct H as [H1 H2]. split; [apply (all_disjoint_set E r rs i rg wlo whi H1 Hi) | exact (IH i rg wlo whi H2 Hi)].
Qed.
Lemma regions_wf_set : forall rs i rg', regions_wf rs = true -> region_wf rg' = true -> regions_wf (list_set rs i rg') = true.
Proof using.
intros rs. induction rs as [|r rs IH]; intros [|i] rg' H Hw; cbn in H |- *; try exact H.
- apply andb_prop in H as [_ H2]. rewrite Hw, H2. reflexivity.
- apply andb_prop in H as [H1 H2]. rewrite H1, (IH i rg' H2 Hw). reflexivity.
Qed.
Lemma Forall_set : forall {X} (P : X -> Prop) l i x, Forall P l -> P x -> Forall P (list_set l i x).
Proof using.
intros X P l. induction l as [|y l IH]; intros [|i] x H Hx; cbn; [exact H | exact H | |]; inversion H; subst; constructor; auto.
Qed.
Lemma st_ok_rewin : forall E ss ms (i : nat) rg (wlo whi : Z),
st_ok ubs0segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_wlo rg <= wlo -> whi <= r_whi rg ->
region_wf (rewin rg wlo whi) = true ->
st_ok ubs0segs E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (list_set (ss_mem ss) i (rewin rg wlo whi)) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros E ss ms i rg wlo whi HS Hi Hlo Hhi Hwf. pose proof HS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & (W & R & D) & A9).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [| exact A9]. cbn [ss_mem]. split; [apply (regions_wf_set _ i _ W Hwf)|]. split; [| apply (pairwise_disjoint_set E _ i rg wlo whi D Hi)].
apply Forall_set; [exact R|]. pose proof (proj1 (Forall_forall _ _) R rg (nth_error_In _ _ Hi)) as (B1 & B2 & B3 & B4).
unfold region_ok, rewin. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]. split; [exact B1|]. split; [exact B2|]. split; [| exact B4].
intros o Ho. apply B3. lia.
Qed.
Fixpoint subwinb (rs' rs : smem) : bool :=
match rs', rs with
| [], [] => true
| r' :: t', r :: t =>
(match r_base r', r_base r with Some a, Some b => Nat.eqb a b | None, None => true | _, _ => false end) &&
((r_whi r' <=? r_wlo r') || ((r_wlo r <=? r_wlo r') && (r_whi r' <=? r_whi r))) && subwinb t' t
| _, _ => false
end.
Lemma in_wrange_subwin : forall E rs' rs a, subwinb rs' rs = true -> in_wrange E rs' a -> in_wrange E rs a.
Proof using.
intros E rs'. induction rs' as [|r' t' IH]; intros [|r t] a H (x & Hin & Hx); cbn in H; try discriminate H; [destruct Hin|].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
destruct Hin as [<-|Hin].
- exists r. split; [left; reflexivity|].
assert (Hb : base_val E (r_base r') = base_val E (r_base r)).
{ destruct (r_base r') as [a'|], (r_base r) as [b'|]; try discriminate H1; [apply Nat.eqb_eq in H1; rewrite H1; reflexivity | reflexivity]. }
rewrite <- Hb. apply Bool.orb_prop in H2. destruct H2 as [H2|H2]; [apply Z.leb_le in H2; lia|].
apply andb_prop in H2 as [H2 H4]. apply Z.leb_le in H2. apply Z.leb_le in H4. lia.
- destruct (IH t a H3 (ex_intro _ x (conj Hin Hx))) as (y & Hy & Hyy). exists y. split; [right; exact Hy | exact Hyy].
Qed.
Lemma region_kept_live : forall E (mem mem' : word -> option byte) r n b m,
r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall i, 0 <= i < m -> mbyte ubs0segs mem' (b + i) = mbyte ubs0segs mem (b + i)) ->
(forall i, r_wlo r <= i < r_whi r -> writable_at ubs0segs mem' (b + i)) ->
0 <= r_lo r -> r_hi r <= m ->
region_kept ubs0segs E mem mem' r.
Proof using.
intros E mem mem' r n b m Hb Hn Hk Hw Hlo Hhi. split; rewrite Hb; cbn [base_val]; rewrite Hn; intros a Ha.
- replace a with (b + (a - b)) by lia. apply Hk. lia.
- intros _. replace a with (b + (a - b)) by lia. apply Hw. lia.
Qed.
Lemma cgif_fp_in : forall g s N b n a,
In (b, n) (cgif_blocks0 g s N) -> b <= a < b + n -> inFP (blocks_fp (cgif_blocks0 g s N)) a.
Proof using. intros g s N b n a Hin Ha. apply inFP_blocks_fp. exists b, n. auto. Qed.
Lemma rc_int_range : forall v, 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= rc_int v < 2 ^ 31.
Proof using. intros v Hv. unfold rc_int. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma rc_int_mod32 : forall c, - 2 ^ 31 <= c < 2 ^ 31 -> rc_int (c mod 2 ^ 32) = c.
Proof using.
intros c Hc. unfold rc_int. destruct (Z_lt_le_dec c 0).
- replace (c mod 2 ^ 32) with (c + 2 ^ 32) by (symmetry; rewrite <- (Z.mod_add c 1 (2 ^ 32)) by lia; apply Z.mod_small; lia).
destruct (Z.ltb_spec (c + 2 ^ 32) (2 ^ 31)); lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec c (2 ^ 31)); lia.
Qed.
Definition af_live (mem : word -> option byte) (s : cgif_st) (N : Z) (GPAL : list Z) (gs : YO07.gif_st) : Prop :=
rc_int (rw_cur s) = YO07.s_rcur gs /\ rw_attr s = raw_attr_of (cg_attr s) /\ cg_ihead s = YO07.s_ihead gs /\
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) /\
oframe_relb false mem N (nth 0 (cg_frames s) None) (YO07.s_q0 gs) /\
oframe_relb true mem N (nth 1 (cg_frames s) None) (YO07.s_q1 gs) /\
oframe_relb true mem N (nth 2 (cg_frames s) None) (YO07.s_q2 gs).
Lemma cgif_rel_split : forall mem md s N GPAL gs,
cgif_rel mem md s N GPAL gs <->
((rc_int (cg_cur s) = YO07.s_cur gs /\ cgif_occ s gs) /\ sink_at ubs0_msyms mem md (cg_file s) (concat (YO07.s_out gs)) /\ (cgif_live gs -> af_live mem s N GPAL gs)).
Proof using. intros. unfold cgif_rel, af_live. tauto. Qed.
Lemma af_live_set_cur : forall mem s N GPAL gs c, af_live mem (set_cur s c) N GPAL gs <-> af_live mem s N GPAL gs.
Proof using. intros. unfold af_live, set_cur. cbn. tauto. Qed.
Lemma cgif_occ_set_cur : forall s c gs, cgif_occ (set_cur s c) gs <-> cgif_occ s gs.
Proof using. intros. unfold cgif_occ, set_cur. cbn. tauto. Qed.
Lemma cgif_occ_ext : forall s s' gs gs', cg_frames s' = cg_frames s ->
YO07.s_q0 gs' = YO07.s_q0 gs -> YO07.s_q1 gs' = YO07.s_q1 gs -> YO07.s_q2 gs' = YO07.s_q2 gs ->
cgif_occ s gs -> cgif_occ s' gs'.
Proof using. intros s s' gs gs' Hf H0 H1 H2 H. unfold cgif_occ in *. rewrite Hf, H0, H1, H2. exact H. Qed.
Lemma cgif_rel_occ : forall mem md s N GPAL gs, cgif_rel mem md s N GPAL gs -> cgif_occ s gs.
Proof using. intros mem md s N GPAL gs ((_ & H) & _). exact H. Qed.
Definition af_vblocks (s : cgif_st) (N : Z) : list (Z * Z) :=
pal_blocks s ++ flat_map (fun o => match o with Some f => (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) | None => [] end) (cg_frames s).
Lemma af_vblocks_sub0 : forall s N x, In x (af_vblocks s N) -> In x (pal_blocks s ++ frames_blocks N (cg_frames s)).
Proof using.
intros s N x Hx. unfold af_vblocks in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right].
unfold frames_blocks. apply in_flat_map in Hx as (o & Ho & Hx). apply in_flat_map. exists o. split; [exact Ho|].
destruct o as [f|]; [| exact Hx]. unfold frame_blocks. right. exact Hx.
Qed.
Lemma af_vblocks_sub : forall g s N x, In x (af_vblocks s N) -> In x (cgif_blocks0 g s N).
Proof using. intros g s N x Hx. unfold cgif_blocks0. right. right. exact (af_vblocks_sub0 s N x Hx). Qed.
Lemma frame_relb_kept : forall wg mem mem' N f fr,
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
Lemma af_live_kept : forall mem mem' s N GPAL gs,
cgif_wf s N ->
(forall a n k, In (a, n) (af_vblocks s N) -> 0 <= k < n -> mbyte ubs0segs mem' (a + k) = mbyte ubs0segs mem (a + k)) ->
af_live mem s N GPAL gs -> af_live mem' s N GPAL gs.
Proof using.
intros mem mem' s N GPAL gs Hwf K (R1 & R2 & R3 & R4 & F0 & F1 & F2).
pose proof Hwf as (Hlen & _).
assert (FR : forall wg j q, oframe_relb wg mem N (nth j (cg_frames s) None) q -> oframe_relb wg mem' N (nth j (cg_frames s) None) q).
{ intros wg j q H. destruct (nth j (cg_frames s) None) as [f|] eqn:Hn; destruct q as [fr|]; cbn [oframe_relb] in H |- *; try exact H.
assert (Hin : In (Some f) (cg_frames s)).
{ rewrite <- Hn. apply nth_In. destruct (Nat.lt_ge_cases j (length (cg_frames s))) as [Hl|Hl]; [exact Hl|]. rewrite (nth_overflow _ _ Hl) in Hn. discriminate Hn. }
apply (frame_relb_kept wg mem mem' N f fr); [| | exact H].
- intros k Hk. apply (K (fr_img f) N k); [| exact Hk]. unfold af_vblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
- intros Hz k Hk. apply (K (fr_lpal f) (3 * fr_nlp f) k); [| exact Hk]. unfold af_vblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin|].
right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]. }
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [| split; [apply FR; exact F0 | split; [apply FR; exact F1 | apply FR; exact F2]]].
intros Hz. destruct (R4 Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (cg_pal s + (a - cg_pal s)) by lia. apply (K (cg_pal s) (3 * cg_ngp s)); [| lia]. unfold af_vblocks. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
Qed.
Definition wgk (k : nat) : bool := match k with 0%nat => false | _ => true end.
Definition af_hdr (mem : word -> option byte) (s : cgif_st) (GPAL : list Z) (gs : YO07.gif_st) : Prop :=
rc_int (rw_cur s) = YO07.s_rcur gs /\ rw_attr s = raw_attr_of (cg_attr s) /\ cg_ihead s = YO07.s_ihead gs /\
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s).
Definition af_slots (mem : word -> option byte) (s : cgif_st) (N : Z) (gs : YO07.gif_st) (P : nat -> Prop) : Prop :=
forall k, (k < 3)%nat -> P k -> oframe_relb (wgk k) mem N (nth k (cg_frames s) None) (qslot gs k).
Lemma af_live_iff : forall mem s N GPAL gs, af_live mem s N GPAL gs <-> af_hdr mem s GPAL gs /\ af_slots mem s N gs (fun _ => True).
Proof using.
intros. unfold af_live, af_hdr, af_slots. split.
- intros (A & B & C & D & F0 & F1 & F2). split; [tauto|]. intros k Hk _. destruct k as [|[|[|k]]]; cbn [wgk qslot]; [exact F0 | exact F1 | exact F2 | lia].
- intros ((A & B & C & D) & F). pose proof (F 0%nat ltac:(lia) I) as F0. pose proof (F 1%nat ltac:(lia) I) as F1. pose proof (F 2%nat ltac:(lia) I) as F2.
cbn [wgk qslot] in F0, F1, F2. tauto.
Qed.
Lemma af_slots_mono : forall mem s N gs (P Q : nat -> Prop), (forall k, Q k -> P k) -> af_slots mem s N gs P -> af_slots mem s N gs Q.
Proof using. intros mem s N gs P Q HPQ H k Hk HQ. exact (H k Hk (HPQ k HQ)). Qed.
Lemma af_hdr_kept : forall mem mem' s GPAL gs,
(Z.land (cg_attr s) 4 = 0 -> forall k, 0 <= k < 3 * cg_ngp s -> mbyte ubs0segs mem' (cg_pal s + k) = mbyte ubs0segs mem (cg_pal s + k)) ->
af_hdr mem s GPAL gs -> af_hdr mem' s GPAL gs.
Proof using.
intros mem mem' s GPAL gs K (A & B & C & D). split; [exact A|]. split; [exact B|]. split; [exact C|].
intros Hz. destruct (D Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (cg_pal s + (a - cg_pal s)) by lia. apply (K Hz). lia.
Qed.
Definition af_fvb (N : Z) (o : option frame_st) : list (Z * Z) :=
match o with Some f => (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) | None => [] end.
Lemma af_vblocks_eq : forall s N, af_vblocks s N = pal_blocks s ++ flat_map (af_fvb N) (cg_frames s).
Proof using. intros. reflexivity. Qed.
Lemma af_fvb_sub : forall N l x, In x (flat_map (af_fvb N) l) -> In x (frames_blocks N l).
Proof using.
intros N l x Hx. unfold frames_blocks. apply in_flat_map in Hx as (o & Ho & Hx). apply in_flat_map. exists o. split; [exact Ho|].
destruct o as [f|]; [| exact Hx]. unfold frame_blocks. right. exact Hx.
Qed.
Lemma af_slots_kept : forall mem mem' s N gs (P : nat -> Prop),
(forall k f, (k < 3)%nat -> P k -> nth k (cg_frames s) None = Some f ->
forall a n j, In (a, n) (af_fvb N (Some f)) -> 0 <= j < n -> mbyte ubs0segs mem' (a + j) = mbyte ubs0segs mem (a + j)) ->
af_slots mem s N gs P -> af_slots mem' s N gs P.
Proof using.
intros mem mem' s N gs P K H k Hk HP. pose proof (H k Hk HP) as Ho.
destruct (nth k (cg_frames s) None) as [f|] eqn:Hn; destruct (qslot gs k) as [fr|]; cbn [oframe_relb] in Ho |- *; try exact Ho.
apply (frame_relb_kept (wgk k) mem mem' N f fr); [| | exact Ho].
- intros j Hj. apply (K k f Hk HP Hn (fr_img f) N j); [left; reflexivity | exact Hj].
- intros Hz j Hj. apply (K k f Hk HP Hn (fr_lpal f) (3 * fr_nlp f) j); [| exact Hj].
cbn [af_fvb]. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity].
Qed.
Lemma af_slots_occ : forall mem s N gs, af_slots mem s N gs (fun _ => True) -> cgif_occ s gs.
Proof using.
intros mem s N gs H. unfold cgif_occ.
pose proof (oframe_relb_occ _ _ _ _ _ (H 0%nat ltac:(lia) I)) as H0. pose proof (oframe_relb_occ _ _ _ _ _ (H 1%nat ltac:(lia) I)) as H1.
pose proof (oframe_relb_occ _ _ _ _ _ (H 2%nat ltac:(lia) I)) as H2. cbn [qslot] in H0, H1, H2. tauto.
Qed.
Lemma cgif_occ_iff : forall s gs, cgif_occ s gs <-> forall k, (k < 3)%nat -> (nth k (cg_frames s) None = None <-> qslot gs k = None).
Proof using.
intros s gs. unfold cgif_occ. split.
- intros (H0 & H1 & H2) [|[|[|k]]] Hk; cbn [qslot]; [exact H0 | exact H1 | exact H2 | lia].
- intros H. pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 1%nat ltac:(lia)) as H1. pose proof (H 2%nat ltac:(lia)) as H2. cbn [qslot] in H0, H1, H2. tauto.
Qed.
Lemma nth_upd_frame : forall s ih fh' k, length (cg_frames s) = 3%nat -> (ih < 3)%nat ->
nth k (cg_frames (upd_frame s ih fh')) None = if (k =? ih)%nat then Some fh' else nth k (cg_frames s) None.
Proof using.
intros s ih fh' k Hlen Hih. unfold upd_frame, set_frames. cbn [cg_frames].
destruct (Nat.eqb_spec k ih) as [->|Hne]; [apply nth_list_set_same; rewrite Hlen; exact Hih | apply nth_list_set_other; lia].
Qed.
Lemma af_slots_upd : forall mem s N gs ih fh' fr' (P : nat -> Prop),
(ih < 3)%nat -> length (cg_frames s) = 3%nat ->
af_slots mem s N gs (fun k => k <> ih /\ P k) -> (P ih -> frame_relb (wgk ih) mem N fh' fr') ->
af_slots mem (upd_frame s ih fh') N (YO07.q_set gs (Z.of_nat ih) (Some fr')) P.
Proof using.
intros mem s N gs ih fh' fr' P Hih Hlen H Hnew k Hk HP. rewrite (nth_upd_frame s ih fh' k Hlen Hih), (qslot_set gs ih _ k Hk Hih).
destruct (Nat.eqb_spec k ih) as [->|Hne]; [cbn [oframe_relb]; exact (Hnew HP) | exact (H k Hk (conj Hne HP))].
Qed.
Lemma af_slots_upd_same : forall mem s N gs ih fh' fr' (P : nat -> Prop),
(ih < 3)%nat -> length (cg_frames s) = 3%nat ->
af_slots mem s N gs (fun k => k <> ih /\ P k) -> qslot gs ih = Some fr' -> (P ih -> frame_relb (wgk ih) mem N fh' fr') ->
af_slots mem (upd_frame s ih fh') N gs P.
Proof using.
intros mem s N gs ih fh' fr' P Hih Hlen H Hq Hnew k Hk HP. rewrite (nth_upd_frame s ih fh' k Hlen Hih).
destruct (Nat.eqb_spec k ih) as [->|Hne]; [rewrite Hq; cbn [oframe_relb]; exact (Hnew HP) | exact (H k Hk (conj Hne HP))].
Qed.
Lemma af_slots_upd_skip : forall mem s N gs ih fh' (P : nat -> Prop),
(ih < 3)%nat -> length (cg_frames s) = 3%nat ->
af_slots mem s N gs P -> (forall k, P k -> k <> ih) -> af_slots mem (upd_frame s ih fh') N gs P.
Proof using.
intros mem s N gs ih fh' P Hih Hlen H HP k Hk HPk. rewrite (nth_upd_frame s ih fh' k Hlen Hih).
destruct (Nat.eqb_spec k ih) as [->|Hne]; [exfalso; exact (HP ih HPk eq_refl) | exact (H k Hk HPk)].
Qed.
Lemma af_hdr_ext2 : forall mem s s' GPAL gs gs',
rw_cur s' = rw_cur s -> rw_attr s' = rw_attr s -> cg_attr s' = cg_attr s -> cg_pal s' = cg_pal s -> cg_ngp s' = cg_ngp s ->
YO07.s_rcur gs' = YO07.s_rcur gs -> cg_ihead s' = YO07.s_ihead gs' ->
af_hdr mem s GPAL gs -> af_hdr mem s' GPAL gs'.
Proof using.
intros mem s s' GPAL gs gs' E1 E2 E3 E5 E6 E7 E8 (A & B & C & D). unfold af_hdr. rewrite E1, E2, E3, E5, E6, E7.
split; [exact A|]. split; [exact B|]. split; [exact E8 | exact D].
Qed.
Lemma af_slots_fill : forall mem s N gs i fn fr (P : nat -> Prop),
af_slots mem s N gs (fun k => k <> i /\ P k) -> nth i (cg_frames s) None = Some fn -> qslot gs i = Some fr -> (P i -> frame_relb (wgk i) mem N fn fr) ->
af_slots mem s N gs P.
Proof using.
intros mem s N gs i fn fr P H Hn Hq Hnew k Hk HP.
destruct (Nat.eq_dec k i) as [->|Hne]; [rewrite Hn, Hq; cbn [oframe_relb]; exact (Hnew HP) | exact (H k Hk (conj Hne HP))].
Qed.
Lemma af_slots_qext : forall mem s N gs gs' (P : nat -> Prop),
(forall k, (k < 3)%nat -> P k -> qslot gs' k = qslot gs k) -> af_slots mem s N gs P -> af_slots mem s N gs' P.
Proof using. intros mem s N gs gs' P E H k Hk HP. rewrite (E k Hk HP). exact (H k Hk HP). Qed.
Lemma af_slots_fext : forall mem s s' N gs (P : nat -> Prop),
cg_frames s' = cg_frames s -> af_slots mem s N gs P -> af_slots mem s' N gs P.
Proof using. intros mem s s' N gs P E H k Hk HP. rewrite E. exact (H k Hk HP). Qed.
Lemma af_hdr_set_cur : forall mem s GPAL gs c, af_hdr mem (set_cur s c) GPAL gs <-> af_hdr mem s GPAL gs.
Proof using. intros. unfold af_hdr, set_cur. cbn. tauto. Qed.
Lemma af_hdr_ext : forall mem s s' GPAL gs gs',
rw_cur s' = rw_cur s -> rw_attr s' = rw_attr s -> cg_attr s' = cg_attr s -> cg_ihead s' = cg_ihead s -> cg_pal s' = cg_pal s -> cg_ngp s' = cg_ngp s ->
YO07.s_rcur gs' = YO07.s_rcur gs -> YO07.s_ihead gs' = YO07.s_ihead gs ->
af_hdr mem s GPAL gs -> af_hdr mem s' GPAL gs'.
Proof using. intros mem s s' GPAL gs gs' E1 E2 E3 E4 E5 E6 E7 E8 H. unfold af_hdr in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8. exact H. Qed.
Lemma cgif_occ_upd : forall s gs ih fh' fr', (ih < 3)%nat -> length (cg_frames s) = 3%nat ->
cgif_occ s gs -> cgif_occ (upd_frame s ih fh') (YO07.q_set gs (Z.of_nat ih) (Some fr')).
Proof using.
intros s gs ih fh' fr' Hih Hlen H. apply (proj2 (cgif_occ_iff _ _)). pose proof (proj1 (cgif_occ_iff _ _) H) as HK. intros k Hk.
rewrite (nth_upd_frame s ih fh' k Hlen Hih), (qslot_set gs ih _ k Hk Hih).
destruct (Nat.eqb_spec k ih) as [->|Hne]; [split; intros X; discriminate X | exact (HK k Hk)].
Qed.
Lemma af_hdr_upd : forall mem s GPAL gs ih fh' o, af_hdr mem s GPAL gs -> af_hdr mem (upd_frame s ih fh') GPAL (YO07.q_set gs (Z.of_nat ih) o).
Proof using.
intros mem s GPAL gs ih fh' o (A & B & C & D). pose proof (q_set_fields gs (Z.of_nat ih) o) as (_ & E1 & _ & E2).
unfold af_hdr. cbn [upd_frame set_frames rw_cur rw_attr cg_attr cg_ihead cg_pal cg_ngp]. rewrite E1, E2. exact (conj A (conj B (conj C D))).
Qed.
Definition ocnt (o : option YO07.frame) : Z := match o with Some _ => 1 | None => 0 end.
Lemma qcount_slots : forall gs, qcount gs = ocnt (qslot gs 0) + ocnt (qslot gs 1) + ocnt (qslot gs 2).
Proof using. intros gs. reflexivity. Qed.
Lemma qcount_af_tail : forall G attr gen delay ctrans nlp lpal img s1 (i : nat), (i = 1%nat \/ i = 2%nat) -> qslot s1 i = None ->
qcount (af_tail G attr gen delay ctrans nlp lpal img s1 (Z.of_nat i)) = qcount s1 + 1.
Proof using.
intros G attr gen delay ctrans nlp lpal img s1 i Hi Hq.
pose proof (af_tail_facts G attr gen delay ctrans nlp lpal img s1 i Hi) as (_ & _ & _ & _ & Q5 & Q6 & Q7). cbv zeta in Q5, Q6, Q7.
rewrite !qcount_slots. destruct Hi as [-> | ->]; cbn [Nat.sub] in Q6.
- rewrite Q5, Q6, (Q7 2%nat ltac:(lia) ltac:(lia) ltac:(lia)). change (qslot s1 1) with (qslot s1 1%nat) in Hq. rewrite Hq.
destruct (qslot s1 0), (YO07.flag (YO07.g_attr G) 8), (YO07.flag attr 2); cbn; lia.
- rewrite Q5, Q6, (Q7 0%nat ltac:(lia) ltac:(lia) ltac:(lia)). rewrite Hq.
destruct (qslot s1 1), (YO07.flag (YO07.g_attr G) 8), (YO07.flag attr 2); cbn; lia.
Qed.
Definition af_newf (mem : word -> option byte) (N : Z) (fn : frame_st) (fattr fgen delay nlp tidx : Z) (IMG LPAL : list Z) (disp tcur : Z) : Prop :=
fr_attr fn = fattr /\ fr_gen fn = fgen /\ fr_delay fn = delay /\ fr_nlp fn = nlp /\ (Z.land fattr 6 <> 0 -> fr_ctidx fn = tidx) /\
fr_disp fn = disp /\ fr_tidx fn = tcur /\
garr8 ubs0segs mem (fr_img fn) IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 ubs0segs mem (fr_lpal fn) LPAL /\ Z.of_nat (length LPAL) = 3 * nlp).
Lemma af_newf_rel : forall mem N fn fattr fgen delay nlp tidx IMG LPAL G wg,
let nf := YO07.new_frame G fattr fgen delay tidx nlp LPAL IMG in
af_newf mem N fn fattr fgen delay nlp tidx IMG LPAL (YO07.f_disp nf) (YO07.f_trans nf) -> frame_relb wg mem N fn nf.
Proof using.
intros mem N fn fattr fgen delay nlp tidx IMG LPAL G wg nf (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl). subst nf.
unfold frame_relb, YO07.new_frame. cbn [YO07.f_attr YO07.f_gen YO07.f_delay YO07.f_nlp YO07.f_ctrans YO07.f_disp YO07.f_trans YO07.f_img YO07.f_lpal].
cbn [YO07.f_disp YO07.f_trans YO07.new_frame] in A6, A7.
split; [exact A1|]. split; [destruct wg; [exact A2 | exact I]|]. split; [exact A3|]. split; [exact A4|].
split; [intros H6; rewrite A1 in H6; rewrite (A5 H6); unfold YO07.flag; destruct (Z.eqb_spec (Z.land fattr 6) 0); [lia | reflexivity]|].
split; [exact A6|]. split; [exact A7|]. split; [exact Hi|]. split; [exact Hil|].
intros H1. rewrite A1 in H1. rewrite A4. exact (Hl H1).
Qed.
Lemma af_newf_kept : forall mem mem' N fn fattr fgen delay nlp tidx IMG LPAL disp tcur,
(forall j, 0 <= j < N -> mbyte ubs0segs mem' (fr_img fn + j) = mbyte ubs0segs mem (fr_img fn + j)) ->
(Z.land fattr 1 <> 0 -> forall j, 0 <= j < 3 * nlp -> mbyte ubs0segs mem' (fr_lpal fn + j) = mbyte ubs0segs mem (fr_lpal fn + j)) ->
af_newf mem N fn fattr fgen delay nlp tidx IMG LPAL disp tcur -> af_newf mem' N fn fattr fgen delay nlp tidx IMG LPAL disp tcur.
Proof using.
intros mem mem' N fn fattr fgen delay nlp tidx IMG LPAL disp tcur Ki Kl (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl).
do 7 (split; [assumption|]). split; [| split; [exact Hil|]].
- eapply garr8_frame; [exact Hi|]. intros a Ha. replace a with (fr_img fn + (a - fr_img fn)) by lia. apply Ki. lia.
- intros H1. destruct (Hl H1) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (fr_lpal fn + (a - fr_lpal fn)) by lia. apply (Kl H1). lia.
Qed.
Lemma af_newf_fields : forall mem N fn fn' fattr fgen delay nlp tidx IMG LPAL disp tcur disp' tcur',
af_newf mem N fn fattr fgen delay nlp tidx IMG LPAL disp tcur ->
fr_attr fn' = fr_attr fn -> fr_gen fn' = fr_gen fn -> fr_delay fn' = fr_delay fn -> fr_nlp fn' = fr_nlp fn -> fr_ctidx fn' = fr_ctidx fn ->
fr_img fn' = fr_img fn -> fr_lpal fn' = fr_lpal fn -> fr_disp fn' = disp' -> fr_tidx fn' = tcur' ->
af_newf mem N fn' fattr fgen delay nlp tidx IMG LPAL disp' tcur'.
Proof using.
intros mem N fn fn' fattr fgen delay nlp tidx IMG LPAL disp tcur disp' tcur' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl) E1 E2 E3 E4 E5 E6 E7 E8 E9.
unfold af_newf. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Hi|]. split; [exact Hil|]. exact Hl.
Qed.
Lemma flush_upd_blocks0 : forall g s N i gen' rwcur', (i < length (cg_frames s))%nat -> cgif_blocks0 g (flush_upd s i gen' rwcur') N = cgif_blocks0 g s N.
Proof using.
intros g s N i gen' rwcur' Hi. pose proof (flush_upd_blocks g s N i gen' rwcur' Hi) as H. unfold cgif_blocks in H. unfold cgif_blocks0.
assert (H1 : forall (a b c : Z * Z) l l', a :: b :: c :: l = a :: b :: c :: l' -> l = l') by (intros a b c l l' E; injection E as E1; exact E1).
apply H1 in H. cbn [cg_raw cg_file flush_upd] in H |- *. rewrite H. reflexivity.
Qed.
Lemma cgif_blocks0_of : forall g s N, cgif_blocks0 g s N = match cgif_blocks g s N with a :: b :: _ :: l => a :: b :: l | _ => nil end.
Proof using. intros. reflexivity. Qed.
Lemma cgif_blocks_front0 : forall g s N, Permutation (cgif_blocks g s N) ((cg_file s, FILE_BLOCK) :: cgif_blocks0 g s N).
Proof using.
intros g s N. unfold cgif_blocks0.
change (cgif_blocks g s N) with ([(g, CGIF_SIZE); (cg_raw s, RAW_SIZE)] ++ (cg_file s, FILE_BLOCK) :: (pal_blocks s ++ frames_blocks N (cg_frames s))).
change ((cg_file s, FILE_BLOCK) :: (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s))
with ((cg_file s, FILE_BLOCK) :: [(g, CGIF_SIZE); (cg_raw s, RAW_SIZE)] ++ (pal_blocks s ++ frames_blocks N (cg_frames s))).
apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma cgif_blocks_upd_frame0 : forall g s N i f f',
nth_error (cg_frames s) i = Some (Some f) -> frame_blocks N f' = frame_blocks N f -> cgif_blocks0 g (upd_frame s i f') N = cgif_blocks0 g s N.
Proof using. intros g s N i f f' H1 H2. rewrite !cgif_blocks0_of, (cgif_blocks_upd_frame g s N i f f' H1 H2). reflexivity. Qed.
Lemma cgif_blocks_set_ihead0 : forall g s N ih, cgif_blocks0 g (set_ihead s ih) N = cgif_blocks0 g s N.
Proof using. intros. reflexivity. Qed.
Lemma cgif_blocks_shift0 : forall g s o1 o2 N,
cgif_blocks0 g (set_frames s [o1; o2; None]) N = cgif_blocks0 g (set_frames s [None; o1; o2]) N.
Proof using. intros. rewrite !cgif_blocks0_of, cgif_blocks_shift. reflexivity. Qed.
Lemma cgif_blocks_ins_frame0 : forall g s N i f',
nth_error (cg_frames s) i = Some None ->
Permutation (cgif_blocks0 g (upd_frame s i f') N) (frame_blocks N f' ++ cgif_blocks0 g s N).
Proof using.
intros g s N i f' Hi. apply (@Permutation_cons_inv _ (cgif_blocks0 g (upd_frame s i f') N) (frame_blocks N f' ++ cgif_blocks0 g s N) (cg_file s, FILE_BLOCK)).
eapply Permutation_trans; [apply Permutation_sym; apply (cgif_blocks_front0 g (upd_frame s i f') N)|].
eapply Permutation_trans; [apply (cgif_blocks_ins_frame g s N i f' Hi)|].
eapply Permutation_trans; [apply Permutation_app_head; apply cgif_blocks_front0|]. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma perm_frame0_front0 : forall g s N f0 o1 o2 X,
cg_frames s = [Some f0; o1; o2] ->
Permutation (cgif_blocks0 g s N ++ X) (frame_blocks N f0 ++ cgif_blocks0 g (set_frames s [None; o1; o2]) N ++ X).
Proof using.
intros g s N f0 o1 o2 X H. apply (@Permutation_cons_inv _ (cgif_blocks0 g s N ++ X) (frame_blocks N f0 ++ cgif_blocks0 g (set_frames s [None; o1; o2]) N ++ X) (cg_file s, FILE_BLOCK)).
eapply Permutation_trans. { change ((cg_file s, FILE_BLOCK) :: cgif_blocks0 g s N ++ X) with (((cg_file s, FILE_BLOCK) :: cgif_blocks0 g s N) ++ X). apply Permutation_app_tail. apply Permutation_sym. apply cgif_blocks_front0. }
eapply Permutation_trans; [apply (perm_frame0_front g s N f0 o1 o2 X H)|].
eapply Permutation_trans. { apply Permutation_app_head. change (cgif_blocks g (set_frames s [None; o1; o2]) N ++ X) with (cgif_blocks g (set_frames s [None; o1; o2]) N ++ X). apply (Permutation_app_tail X (cgif_blocks_front0 g (set_frames s [None; o1; o2]) N)). }
cbn [app]. change (cg_file (set_frames s [None; o1; o2])) with (cg_file s). apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma cgif_rel_kept_all : forall (m m' : word -> option byte) md s N GPAL gs,
cgif_wf s N -> (forall a, mbyte ubs0segs m' a = mbyte ubs0segs m a) -> cgif_rel m md s N GPAL gs -> cgif_rel m' md s N GPAL gs.
Proof using.
intros m m' md s N GPAL gs Hwf K H. apply (proj2 (cgif_rel_split _ _ _ _ _ _)). apply (proj1 (cgif_rel_split _ _ _ _ _ _)) in H as (H1 & H2 & H3).
split; [exact H1|]. split; [apply (sink_at_frame ubs0_msyms m m' md); [intros a _; apply K | exact H2]|].
intros Hl. apply (af_live_kept m m' s N GPAL gs Hwf); [intros a n k _ _; apply K | exact (H3 Hl)].
Qed.
Definition af_sink (g : Z) (s0 s : cgif_st) (N : Z) (rest FP : list (Z * Z)) (S : list Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
sink_at ubs0_msyms mem md (cg_file s) S /\ In (cg_file s, FILE_BLOCK) (blocks L A) /\ In (cg_file s, FILE_BLOCK) rest /\
~ sink_open_fp FP /\ fp_avoids FP (cg_file s) (cg_file s + FILE_BLOCK) /\ (forall a, inFP FP a -> inFP (cgif_fp g s0 N) a).
Section h.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Definition af_postX (regs0 : bvmap 5 word) (g N : Z) (s0 : cgif_st) (CB rest : list (Z * Z)) (GPAL : list Z) (gs gsF : YO07.gif_st) (bF : rbound)
L A mem md (c' : config) : Prop :=
exists L' A' regs' mem' md' (s' : cgif_st),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR ADDFRAME_STK (spZ regs0) (cgif_fp g s0 N) L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
cgif_at mem' g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s0 /\ cg_H s' = cg_H s0 /\ cg_attr s' = cg_attr s0 /\ cg_raw s' = cg_raw s0 /\ cg_file s' = cg_file s0 /\
Permutation (blocks L' A') (cgif_blocks0 g s' N ++ CB ++ rest) /\
cg_gen s' = cg_gen s0 /\ cg_ngp s' = cg_ngp s0 /\ cg_pal s' = cg_pal s0 /\
cgif_rel mem' md' s' N GPAL gsF /\
Z.of_nat (length (concat (YO07.s_out gsF))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N /\
res_ok A' bF.
Lemma af_env_blk : img_laws ubs0_msyms MR -> forall L1 A1 m1 md1 bb n a,
heap_ok MR L1 A1 m1 md1 -> In (bb, n) (blocks L1 A1) -> env_addr a -> ~ (bb <= a < bb + n).
Proof using API.
intros IMG L1 A1 m1 md1 bb n a HHx Hin1 Hea Hr. apply blocks_In in Hin1 as (q & Hq & Hqin).
destruct (skl_env ubs0_msyms a Hea) as (Himg1 & _). assert (Hrg : 0 <= a - bb < n) by lia.
apply (il_blocks IMG L1 A1 m1 md1 q n (a - bb) (proj1 HHx) Hqin Hrg). rewrite Hq. replace (bb + (a - bb)) with a by lia. exact Himg1.
Qed.
Lemma af_frame_vsep0 : forall L A m md g s N rest j f a n,
heap_ok MR L A m md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ rest) ->
nth_error (cg_frames s) j = Some (Some f) -> In (a, n) (af_vblocks s N) ->
fr_ptr f + FRAME_SIZE <= a \/ a + n <= fr_ptr f.
Proof using LAWS.
intros L A m md g s N rest j f a n HH HB Hj Hin.
destruct (nth_error_split _ _ Hj) as (l1 & l2 & Hfr & Hl1).
assert (HP : Permutation (cgif_blocks0 g s N ++ rest)
((fr_ptr f, FRAME_SIZE) :: (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) ::
(pal_blocks s ++ frames_blocks N l1 ++ (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) ++ frames_blocks N l2) ++ rest)).
{ unfold cgif_blocks0. rewrite Hfr, frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). unfold frame_blocks at 1.
apply perm_frame_front. }
pose proof (heap_sep_perm _ _ LAWS L A m md (fr_ptr f, FRAME_SIZE) _ (a, n) HH (Permutation_trans HB HP)) as Hs.
cbn [fst snd] in Hs. apply Hs. clear Hs HP.
rewrite af_vblocks_eq, Hfr, flat_map_app in Hin. cbn [flat_map] in Hin.
right. right. apply in_app_iff. left.
apply in_app_iff in Hin as [Hin|Hin]; [apply in_app_iff; left; exact Hin|].
apply in_app_iff. right.
apply in_app_iff in Hin as [Hin|Hin]; [apply in_app_iff; left; exact (af_fvb_sub N l1 _ Hin)|].
apply in_app_iff. right.
cbn [af_fvb app] in Hin.
destruct Hin as [Heq|Hin]; [left; exact Heq | right]. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin | right; exact (af_fvb_sub N l2 _ Hin)].
Qed.
Lemma heap_sep_app : forall L A mem md (l1 l2 : list (Z * Z)) x y,
heap_ok MR L A mem md -> Permutation (blocks L A) (l1 ++ l2) -> In x l1 -> In y l2 ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using LAWS.
intros L A mem md l1 l2 x y HH HP Hx Hy. destruct (in_split _ _ Hx) as (a & b & ->).
apply (heap_sep_perm _ _ LAWS L A mem md x (a ++ b ++ l2) y HH).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym.
replace (a ++ b ++ l2) with (a ++ (b ++ l2)) by reflexivity. apply Permutation_middle.
- apply in_app_iff. right. apply in_app_iff. right. exact Hy.
Qed.
Lemma journal_restart : forall STK sp0 FP FP2 L A mem md L' A' mem' md',
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' -> journal ubs0_msyms MR STK sp0 FP2 L' A' mem' md' L' A' mem' md'.
Proof using API.
intros STK sp0 FP FP2 L A mem md L' A' mem' md' (HH & Hos & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
split; [exact HH|]. split; [apply os_step_refl|]. split; [intros a _ _; split; [reflexivity | tauto]|].
split; [intros; reflexivity|]. split; [intros a n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hst|]. split; [exact Herr | apply img_kept_refl].
Qed.
Lemma af_postX_rebase : forall regs0 g N s0 CB rest GPAL gs gsF bF L A mem md L2 A2 mem2 md2 FPw c',
journal ubs0_msyms MR ADDFRAME_STK (spZ regs0) FPw L A mem md L2 A2 mem2 md2 ->
(forall a, inFP FPw a -> inFP (cgif_fp g s0 N) a) -> (forall a, inFP (cgif_fp g s0 N) a -> a < alloc_ceiling) ->
af_postX regs0 g N s0 CB rest GPAL gs gsF bF L2 A2 mem2 md2 c' -> af_postX regs0 g N s0 CB rest GPAL gs gsF bF L A mem md c'.
Proof using.
intros regs0 g N s0 CB rest GPAL gs gsF bF L A mem md L2 A2 mem2 md2 FPw c' HJ1 Hsub Hlow
(L' & A' & regs' & mem' & md' & s' & Hc & HJ2 & Hrest).
exists L', A', regs', mem', md', s'. split; [exact Hc|]. split; [| exact Hrest].
eapply (journal_sub ubs0_msyms MR); [exact (journal_fp_weaken API _ _ _ _ _ _ _ _ _ _ _ _ Hsub HJ1) | exact HJ2 | lia | lia |].
intros a Ha. split; [exact Ha | exact (Hlow a Ha)].
Qed.
Lemma wr_ok_subwin : forall E rs' rs STK sp0 FP bl0 blc,
subwinb rs' rs = true -> wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E rs' STK sp0 FP bl0 blc.
Proof using. intros E rs' rs STK sp0 FP bl0 blc H W a Ha. apply W. exact (in_wrange_subwin E rs' rs a H Ha). Qed.
Lemma af_fp_sub : forall g s0 s N, cg_pal s = cg_pal s0 -> cg_ngp s = cg_ngp s0 -> cg_attr s = cg_attr s0 -> cg_raw s = cg_raw s0 ->
(forall x, In x (frames_blocks N (cg_frames s)) -> In x (frames_blocks N (cg_frames s0))) ->
forall a, inFP (blocks_fp (cgif_blocks0 g s N)) a -> inFP (cgif_fp g s0 N) a.
Proof using.
intros g s0 s N Hp Hn Ha Hr Hfr a Hin. apply (proj1 (inFP_blocks_fp _ _)) in Hin as (bb & nn & Hbn & Hab).
unfold cgif_fp. apply (proj2 (inFP_cons _ _ _ _)). right. apply (proj2 (inFP_blocks_fp _ _)). exists bb, nn. split; [| exact Hab].
unfold cgif_blocks0 in Hbn. unfold cgif_blocks, pal_blocks. rewrite <- Hp, <- Hn, <- Ha, <- Hr.
destruct Hbn as [Hbn | [Hbn | Hbn]]; [left; exact Hbn | right; left; exact Hbn | right; right; right].
apply in_app_iff in Hbn as [Hbn|Hbn]; apply in_app_iff; [left; exact Hbn | right; apply Hfr; exact Hbn].
Qed.
Lemma af_sink_now : forall STK sp0 g s N L A mem md L' A' mem' md' S rest CB,
journal ubs0_msyms MR STK sp0 (blocks_fp (cgif_blocks0 g s N)) L A mem md L' A' mem' md' ->
heap_ok MR L A mem md -> Permutation (blocks L A) (cgif_blocks0 g s N ++ CB ++ rest) -> In (cg_file s, FILE_BLOCK) rest ->
sink_at ubs0_msyms mem md (cg_file s) S -> sink_at ubs0_msyms mem' md' (cg_file s) S /\ In (cg_file s, FILE_BLOCK) (blocks L' A').
Proof using LAWS.
intros STK sp0 g s N L A mem md L' A' mem' md' S rest CB HJ HH HB Hf HS.
assert (HfLA : In (cg_file s, FILE_BLOCK) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; right; exact Hf).
eapply (sink_kept ubs0_msyms MR); [exact HJ | | exact HfLA | | exact HS].
- unfold sink_open_fp, in_fp. intros (r & Hr & Hrz). unfold blocks_fp in Hr. apply in_map_iff in Hr as ([bb nn] & <- & Hbn). cbn [fst snd] in Hrz.
assert (Hbn' : In (bb, nn) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS L A mem md bb nn HH Hbn') as [R0 R1]. lia.
- intros a Ha Hin. apply (proj1 (inFP_blocks_fp _ _)) in Hin as (bb & nn & Hbn & Hab).
destruct (in_split _ _ Hf) as (r1 & r2 & Hr).
assert (HBf : Permutation (blocks L A) ((cg_file s, FILE_BLOCK) :: cgif_blocks0 g s N ++ CB ++ r1 ++ r2)).
{ eapply Permutation_trans; [exact HB|]. rewrite Hr. rewrite !app_assoc.
apply Permutation_sym. replace ((cg_file s, FILE_BLOCK) :: ((cgif_blocks0 g s N ++ CB) ++ r1) ++ r2) with ((cg_file s, FILE_BLOCK) :: (((cgif_blocks0 g s N ++ CB) ++ r1) ++ r2)) by reflexivity.
apply Permutation_middle. }
pose proof (heap_sep_perm _ _ LAWS L A mem md (cg_file s, FILE_BLOCK) _ (bb, nn) HH HBf ltac:(apply in_app_iff; left; exact Hbn)) as X. cbn [fst snd] in X. lia.
Qed.
Lemma af_sink_at : forall STK sp0 g s0 s N rest FP S L A mem md L' A' mem' md',
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' -> af_sink g s0 s N rest FP S L A mem md ->
sink_at ubs0_msyms mem' md' (cg_file s) S /\ In (cg_file s, FILE_BLOCK) (blocks L' A').
Proof using API.
intros STK sp0 g s0 s N rest FP S L A mem md L' A' mem' md' HJ (HS & Hin & _ & Hno & Hav & _).
exact (sink_kept ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hno Hin Hav HS).
Qed.
End h.
End d.
