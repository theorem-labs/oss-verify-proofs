(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP0l YP06 YP03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AD2f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ext_in (p r : YP09.region) : Prop := r_base p = r_base r /\ r_lo r <= r_lo p /\ r_hi p <= r_hi r.
Lemma extent_disjoint_in : forall E p q r r', ext_in p r -> ext_in q r' -> extent_disjoint E r r' -> extent_disjoint E p q.
Proof.
intros E p q r r' (Bp & Lp & Hp) (Bq & Lq & Hq) D. unfold extent_disjoint in *. rewrite Bp, Bq. lia.
Qed.
Lemma all_disjoint_Forall : forall E r rs, all_disjoint E r rs <-> Forall (extent_disjoint E r) rs.
Proof.
intros E r rs. induction rs as [|x rs IH]; cbn; [split; [intros; constructor | intros; exact I]|].
split; [intros [A B2]; constructor; [exact A | apply IH; exact B2] | intros H; inversion H; subst; split; [assumption | apply IH; assumption]].
Qed.
Lemma extent_disjoint_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. intros E a b. unfold extent_disjoint. lia. Qed.
Inductive refines (E : YP0m.env) (m : word -> option byte) : smem -> list smem -> Prop :=
| refines_nil : refines E m [] []
| refines_cons : forall r rs ps pss,
(region_ok tfibsegs E m r -> Forall (region_ok tfibsegs E m) ps) ->
Forall (fun p => ext_in p r) ps -> pairwise_disjoint E ps ->
refines E m rs pss -> refines E m (r :: rs) (ps :: pss).
Lemma pairwise_disjoint_app : forall E l1 l2,
pairwise_disjoint E l1 -> pairwise_disjoint E l2 -> (forall a b, In a l1 -> In b l2 -> extent_disjoint E a b) -> pairwise_disjoint E (l1 ++ l2).
Proof.
intros E l1 l2. induction l1 as [|x l1 IH]; cbn; intros P1 P2 X; [exact P2|].
destruct P1 as [A1 P1]. split.
- apply all_disjoint_Forall. apply Forall_app. split; [apply all_disjoint_Forall; exact A1|].
apply Forall_forall. intros b Hb. apply X; [left; reflexivity | exact Hb].
- apply IH; [exact P1 | exact P2 |]. intros a b Ha Hb. apply X; [right; exact Ha | exact Hb].
Qed.
Lemma refines_in : forall E m rs pss, refines E m rs pss ->
forall q, In q (concat pss) -> exists r, In r rs /\ ext_in q r.
Proof.
intros E m rs pss H. induction H as [|r rs ps pss Hok Hin Hpd H IH]; cbn; intros q Hq; [destruct Hq|].
apply in_app_or in Hq as [Hq|Hq].
- exists r. split; [left; reflexivity | exact (proj1 (Forall_forall _ _) Hin q Hq)].
- destruct (IH q Hq) as (r' & Hr' & E'). exists r'. split; [right; exact Hr' | exact E'].
Qed.
Theorem mem_ok_refine : forall E m rs pss,
mem_ok tfibsegs E m rs -> refines E m rs pss -> regions_wf (concat pss) = true -> mem_ok tfibsegs E m (concat pss).
Proof.
intros E m rs pss (Hwf & Hok & Hpd) HR Hwf'. split; [exact Hwf'|]. clear Hwf.
revert Hwf' Hok Hpd. induction HR as [|r rs ps pss Hok1 Hin Hpd1 HR IH]; cbn; intros Hwf' Hok Hpd.
- split; [constructor | exact I].
- pose proof (Forall_inv Hok) as Hr. pose proof (Forall_inv_tail Hok) as Hrs. destruct Hpd as [Ad Pd].
assert (W2 : regions_wf (concat pss) = true).
{ clear - Hwf'. induction ps as [|x ps IH]; cbn in *; [exact Hwf'|]. apply andb_prop in Hwf' as [_ H]. exact (IH H). }
destruct (IH W2 Hrs Pd) as [Hok' Hpd']. split.
+ apply Forall_app. split; [exact (Hok1 Hr) | exact Hok'].
+ apply pairwise_disjoint_app; [exact Hpd1 | exact Hpd' |].
intros a b Ha Hb. destruct (refines_in E m rs pss HR b Hb) as (r' & Hr' & Eb).
apply (extent_disjoint_in E a b r r' (proj1 (Forall_forall _ _) Hin a Ha) Eb).
exact (proj1 (Forall_forall _ _) (proj1 (all_disjoint_Forall E r rs) Ad) r' Hr').
Qed.
Lemma chunk_ok_clip : forall E m base c lo hi,
chunk_ok tfibsegs E m base c -> Forall (chunk_ok tfibsegs E m base) (clip_chunk lo hi c).
Proof.
intros E m base [off cv] lo hi Hc. unfold clip_chunk. unfold c_len in *. cbn [YP09.c_off YP09.c_val] in *.
set (a' := Z.max off lo). set (b' := Z.min (off + cv_len cv) hi).
destruct (Z.leb_spec b' a') as [Hle|Hlt]; [constructor|].
assert (Ha : off <= a') by (subst a'; lia). assert (Hb : b' <= off + cv_len cv) by (subst b'; lia).
destruct cv as [w v | zl | il | d s dl]; cbn [cv_len] in *.
- destruct (lo <=? off), (off + Z.of_N w <=? hi); cbn [andb]; first [constructor; [exact Hc | constructor] | constructor].
- constructor; [| constructor]. intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *.
destruct (Hc (a' - off + i) ltac:(cbn [YP09.c_off YP09.c_val c_len cv_len]; lia)) as (b & Hb1 & Hb2). cbn [YP09.c_off YP09.c_val] in Hb1, Hb2.
exists b. split; [exact Hb1|]. replace (base + a' + i) with (base + off + (a' - off + i)) by lia. exact Hb2.
- constructor; [| constructor]. intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *.
destruct (Hc (a' - off + i) ltac:(cbn [YP09.c_off YP09.c_val c_len cv_len]; lia)) as (b & Hb1 & Hb2). cbn [YP09.c_off YP09.c_val] in Hb1, Hb2.
exists b. unfold cbyte in *. unfold img_byte in *. split.
+ rewrite <- Hb1. f_equal. f_equal. lia.
+ replace (base + a' + i) with (base + off + (a' - off + i)) by lia. exact Hb2.
- constructor; [| constructor]. intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *.
destruct (Hc (a' - off + i) ltac:(cbn [YP09.c_off YP09.c_val c_len cv_len]; lia)) as (b & Hb1 & Hb2). cbn [YP09.c_off YP09.c_val] in Hb1, Hb2.
exists b. unfold cbyte in *. split.
+ rewrite <- Hb1. f_equal. lia.
+ replace (base + a' + i) with (base + off + (a' - off + i)) by lia. exact Hb2.
Qed.
Theorem region_ok_clip : forall E m r lo hi,
region_ok tfibsegs E m r -> r_lo r <= hi -> lo <= r_hi r -> region_ok tfibsegs E m (clip_region lo hi r).
Proof.
intros E m r lo hi (B1 & B2 & Wr & C) Hlo Hhi. unfold clip_region, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [lia|]. split; [lia|]. split.
- intros o Ho. destruct (Z.leb_spec (r_whi r) (r_wlo r)); [lia|]. apply Wr. lia.
- induction (r_chunks r) as [|c cs IH]; cbn; [constructor|].
apply Forall_app. split; [apply chunk_ok_clip; exact (Forall_inv C) | apply IH; exact (Forall_inv_tail C)].
Qed.
Lemma clip_ext_in : forall lo hi r, r_lo r <= hi -> lo <= r_hi r -> lo <= hi -> ext_in (clip_region lo hi r) r.
Proof. intros lo hi r H1 H2 H3. unfold ext_in, clip_region. cbn. repeat split; lia. Qed.
Lemma ext_in_refl : forall r, ext_in r r.
Proof. intros r. unfold ext_in. repeat split; lia. Qed.
Lemma ext_in_trans : forall a b c, ext_in a b -> ext_in b c -> ext_in a c.
Proof. intros a b c (B1 & L1 & H1) (B2 & L2 & H2). unfold ext_in. rewrite B1, B2. repeat split; lia. Qed.
Lemma refines_app : forall E m rs1 pss1 rs2 pss2,
refines E m rs1 pss1 -> refines E m rs2 pss2 -> refines E m (rs1 ++ rs2) (pss1 ++ pss2).
Proof. intros E m rs1 pss1 rs2 pss2 H1 H2. induction H1; cbn; [exact H2 | apply refines_cons; assumption]. Qed.
Lemma refines_single : forall E m rs, refines E m rs (map (fun r => [r]) rs).
Proof.
intros E m rs. induction rs as [|r rs IH]; cbn; [constructor|].
apply refines_cons; [intros Hr; constructor; [exact Hr | constructor] | constructor; [apply ext_in_refl | constructor] | cbn; split; exact I | exact IH].
Qed.
Lemma refines_drop_each : forall E m rs, refines E m rs (map (fun _ => @nil YP09.region) rs).
Proof.
intros E m rs. induction rs as [|r rs IH]; cbn; [constructor|].
apply refines_cons; [intros _; constructor | constructor | exact I | exact IH].
Qed.
Definition pieces_ok (E : YP0m.env) (m : word -> option byte) (r : YP09.region) (ps : list YP09.region) : Prop :=
(region_ok tfibsegs E m r -> Forall (region_ok tfibsegs E m) ps) /\ Forall (fun p => ext_in p r) ps /\ pairwise_disjoint E ps
/\ Forall (fun p => r_lo p <= r_hi p) ps.
Lemma refines_map : forall E m (F : YP09.region -> list YP09.region) rs,
(forall r, In r rs -> pieces_ok E m r (F r)) -> refines E m rs (map F rs).
Proof.
intros E m F rs H. induction rs as [|r rs IH]; cbn; [constructor|].
destruct (H r (or_introl eq_refl)) as (P1 & P2 & P3 & _).
apply refines_cons; [exact P1 | exact P2 | exact P3 | apply IH; intros r' Hr'; apply H; right; exact Hr'].
Qed.
Lemma clip_out_ok : forall E m lo hi r, lo <= hi -> r_lo r <= r_hi r -> pieces_ok E m r (clip_out lo hi r).
Proof.
intros E m lo hi r Hlh Hr. unfold clip_out.
destruct ((hi <=? r_lo r) || (r_hi r <=? lo))%bool eqn:Eo.
- split; [intros H; constructor; [exact H | constructor] |]. split; [constructor; [apply ext_in_refl | constructor] |].
split; [cbn; split; exact I |]. constructor; [exact Hr | constructor].
- apply Bool.orb_false_iff in Eo as [E1 E2]. apply Z.leb_gt in E1. apply Z.leb_gt in E2.
split; [| split; [| split]].
+ intros H. apply Forall_app. split.
* destruct (Z.ltb_spec (r_lo r) lo); [| constructor]. constructor; [| constructor]. apply region_ok_clip; [exact H | lia | lia].
* destruct (Z.ltb_spec hi (r_hi r)); [| constructor]. constructor; [| constructor]. apply region_ok_clip; [exact H | lia | lia].
+ apply Forall_app. split.
* destruct (Z.ltb_spec (r_lo r) lo); [| constructor]. constructor; [| constructor]. apply clip_ext_in; lia.
* destruct (Z.ltb_spec hi (r_hi r)); [| constructor]. constructor; [| constructor]. apply clip_ext_in; lia.
+ destruct (Z.ltb_spec (r_lo r) lo), (Z.ltb_spec hi (r_hi r)); cbn [app pairwise_disjoint all_disjoint]; repeat split; try exact I.
unfold extent_disjoint, clip_region. cbn [r_base r_lo r_hi]. left. lia.
+ apply Forall_app. split.
* destruct (Z.ltb_spec (r_lo r) lo); [| constructor]. constructor; [| constructor]. unfold clip_region. cbn [r_lo r_hi]. lia.
* destruct (Z.ltb_spec hi (r_hi r)); [| constructor]. constructor; [| constructor]. unfold clip_region. cbn [r_lo r_hi]. lia.
Qed.
Lemma flat_map_pieces_ok : forall E m (f : YP09.region -> list YP09.region) r ps,
pieces_ok E m r ps -> (forall p, In p ps -> r_lo p <= r_hi p -> pieces_ok E m p (f p)) -> pieces_ok E m r (flat_map f ps).
Proof.
intros E m f r ps (Hok & Hin & Hpd & Hle) Hf. revert Hok Hin Hpd Hle Hf. induction ps as [|p ps IH]; cbn; intros Hok Hin Hpd Hle Hf.
- split; [intros _; constructor|]. split; [constructor|]. split; [exact I | constructor].
- destruct Hpd as [Had Hpd].
destruct (IH (fun H => Forall_inv_tail (Hok H)) (Forall_inv_tail Hin) Hpd (Forall_inv_tail Hle) (fun q Hq Hq' => Hf q (or_intror Hq) Hq'))
as (Iok & Iin & Ipd & Ile).
destruct (Hf p (or_introl eq_refl) (Forall_inv Hle)) as (Pok & Pin & Ppd & Ple).
split; [| split; [| split]].
+ intros H. apply Forall_app. split; [apply Pok; exact (Forall_inv (Hok H)) | apply Iok; exact H].
+ apply Forall_app. split; [| exact Iin]. apply Forall_forall. intros q Hq.
exact (ext_in_trans q p r (proj1 (Forall_forall _ _) Pin q Hq) (Forall_inv Hin)).
+ apply pairwise_disjoint_app; [exact Ppd | exact Ipd |]. intros a b Ha Hb.
apply in_flat_map in Hb as (p' & Hp' & Hb).
assert (Hle' : r_lo p' <= r_hi p') by exact (proj1 (Forall_forall _ _) (Forall_inv_tail Hle) p' Hp').
destruct (Hf p' (or_intror Hp') Hle') as (_ & P'in & _).
apply (extent_disjoint_in E a b p p' (proj1 (Forall_forall _ _) Pin a Ha) (proj1 (Forall_forall _ _) P'in b Hb)).
exact (proj1 (Forall_forall _ _) (proj1 (all_disjoint_Forall E p ps) Had) p' Hp').
+ apply Forall_app. split; [exact Ple | exact Ile].
Qed.
End e.
