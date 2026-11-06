(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the empty-depot switch (DepotCfg.depot_has_trace) taken from proofs/libreac/fuzz_knock/lib/Reusable/YG0j.v at 88154566652a, hunk by hunk (provenance evidence/depot: depot-classes.tsv, depot_apply.py): hunks 1 2 3 4 5; no hunk keeps this file's text. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/Reusable/YG0j.v at 4f87de75d677 (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08 YK0v YK13 YA05 YA06 YG0b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YK0g.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG0f YG0v YG0n YG0s YG08 YG0h DepotCfg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope Z_scope.
Local Notation covered := YK0g.covered.
Local Notation ivs_wf := YK0g.ivs_wf.
Local Notation iv_wf := YK0g.iv_wf.
Lemma cov_app : forall l1 l2 x, covered (l1 ++ l2) x = (covered l1 x || covered l2 x)%bool.
Proof. intros. apply YK0g.covered_app. Qed.
Lemma cov_subtract_out : forall l lo hi x, ivs_wf l -> lo <= hi -> ~ (lo <= x < hi) ->
covered (maps_subtract l lo hi) x = covered l x.
Proof.
intros l lo hi x Hwf Hlh Hx. destruct (YK0g.maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & Cv). rewrite Cv.
unfold YK0g.in_rng. replace ((lo <=? x) && (x <? hi))%bool with false; [apply Bool.andb_true_r|].
symmetry. apply Bool.andb_false_iff. destruct (Z_lt_dec x lo); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.
Lemma cov_lazy_interior_out : forall (a n : word) x,
bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
~ (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n) -> covered (lazy_interior a n) x = false.
Proof.
intros a n x Han Hx. unfold lazy_interior. cbv zeta. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn.
unfold bv_modulus, page_size in *.
set (lo' := (bv_unsigned a + 4096 - 1) / 4096 * 4096). set (hi' := (bv_unsigned a + bv_unsigned n) / 4096 * 4096).
assert (L1 : bv_unsigned a <= lo') by (subst lo'; pose proof (Z_div_mod_eq_full (bv_unsigned a + 4096 - 1) 4096); pose proof (Z.mod_pos_bound (bv_unsigned a + 4096 - 1) 4096); lia).
assert (L2 : hi' <= bv_unsigned a + bv_unsigned n) by (subst hi'; pose proof (Z_div_mod_eq_full (bv_unsigned a + bv_unsigned n) 4096); pose proof (Z.mod_pos_bound (bv_unsigned a + bv_unsigned n) 4096); lia).
destruct (lo' <? hi') eqn:E; [|reflexivity]. apply Z.ltb_lt in E. cbn [covered existsb].
unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. cbn [fst snd].
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; lia). rewrite Bool.orb_false_r.
apply Bool.andb_false_iff. destruct (Z_lt_dec x lo'); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.
Lemma model_ivs_wf_parts : forall md, YK0g.model_ivs_wf md ->
ivs_wf (vm_maps (m_vmmaps md)) /\ ivs_wf (vm_noaccess (m_vmmaps md)) /\ ivs_wf (m_vm_lazy md).
Proof. intros md (H1 & H2 & H3 & _). exact (conj H1 (conj H2 H3)). Qed.
Ltac mproj :=
repeat first [ rewrite YK0g.m_vmmaps_with_vm_backing | rewrite YK0g.m_vm_lazy_with_vm_backing
| rewrite YK0g.m_vmmaps_with_vmmaps | rewrite YK0g.m_vm_lazy_with_vmmaps ].
Lemma cov_grant_md : forall hole flags (addr n : word) md x,
YK0g.model_ivs_wf md -> bv_unsigned addr + bv_unsigned n <= 2 ^ 64 ->
~ (bv_unsigned addr <= x < bv_unsigned addr + bv_unsigned n) ->
covered (vm_noaccess (m_vmmaps (grant_md hole flags addr n md)) ++ m_vm_lazy (grant_md hole flags addr n md)) x
= covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x.
Proof.
intros hole flags addr n md x WF Han Hx. pose proof (model_ivs_wf_parts md WF) as (_ & Wn & Wl).
pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Rn.
unfold grant_md. destruct hole.
- unfold with_mmap_backing. destruct (mmap_noreserve_b flags).
+ unfold vm_add_lazy, mmap_model. mproj. cbn [vm_noaccess]. rewrite !cov_app, (cov_lazy_interior_out addr n x Han Hx). reflexivity.
+ unfold mmap_model. mproj. cbn [vm_noaccess]. reflexivity.
- unfold fixedin_ok_model, with_mmap_replacement, with_mmap_backing, vm_forget_range, fixedin_ok_vmmaps. cbn [Z.eqb].
unfold mmap_fixed_rw_next. destruct (mmap_noreserve_b flags).
+ unfold vm_add_lazy. mproj. cbn [vm_noaccess].
rewrite !cov_app, (cov_lazy_interior_out addr n x Han Hx), !cov_subtract_out by (assumption || lia). reflexivity.
+ mproj. cbn [vm_noaccess]. rewrite !cov_app, !cov_subtract_out by (assumption || lia). reflexivity.
Qed.
Lemma cov_mmap_model : forall flags (a n : word) md x, mmap_noreserve_b flags = false ->
covered (vm_noaccess (m_vmmaps (with_mmap_backing flags a n (mmap_model a n md))) ++ m_vm_lazy (with_mmap_backing flags a n (mmap_model a n md))) x
= covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x.
Proof. intros flags a n md x Hf. unfold with_mmap_backing. rewrite Hf. unfold mmap_model. mproj. cbn [vm_noaccess]. reflexivity. Qed.
Lemma cov_munmap : forall (a n : word) md x,
YK0g.model_ivs_wf md ->
~ (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n) ->
covered (vm_noaccess (m_vmmaps (munmap_model a n md)) ++ m_vm_lazy (munmap_model a n md)) x
= covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x.
Proof.
intros a n md x WF Hx. pose proof (model_ivs_wf_parts md WF) as (_ & Wn & Wl). pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Rn.
unfold munmap_model, with_mmap_destroyed, vm_forget_range. mproj. cbn [vm_noaccess].
rewrite !cov_app, !cov_subtract_out by (assumption || lia). reflexivity.
Qed.
Lemma sum_count_ext_in : forall P Q l,
(forall q x, In q l -> YK0g.B q <= x < YK0g.B q + YK0g.S q -> P x = Q x) ->
YK0g.sum_count P l = YK0g.sum_count Q l.
Proof.
intros P Q l H. induction l as [|q l IH]; [reflexivity|]. cbn [YK0g.sum_count].
rewrite IH by (intros q' x Hq' Hx; exact (H q' x (or_intror Hq') Hx)). f_equal.
unfold YK0g.iv_count. apply YK0g.zcount_ext. intros x Hx. apply (H q x (or_introl eq_refl)).
pose proof (YK0g.S_range q). rewrite Z2Nat.id in Hx by lia. exact Hx.
Qed.
Lemma pairwise_app_mid : forall {X} (R : X -> X -> Prop) l1 x l2,
pairwise R (l1 ++ x :: l2) -> (forall y, In y l1 -> R y x) /\ (forall y, In y l2 -> R x y).
Proof.
intros X R l1 x l2. induction l1 as [|z l1 IH]; cbn [app pairwise]; intros [F P].
- split; [intros y []|]. intros y Hy. exact (proj1 (Forall_forall _ _) F y Hy).
- destruct (IH P) as [A1 A2]. split; [|exact A2]. intros y [<-|Hy]; [|exact (A1 y Hy)].
exact (proj1 (Forall_forall _ _) F x ltac:(apply in_app_iff; right; left; reflexivity)).
Qed.
Lemma wiv_uw : forall e : word * word, wiv (bv_unsigned (fst e), bv_unsigned (snd e)) = e.
Proof. intros [a n]. unfold wiv. cbn [fst snd]. rewrite !w64_uw. reflexivity. Qed.
Lemma esec_single : forall na lz (e : word * word),
esec na lz [(bv_unsigned (fst e), bv_unsigned (snd e))] = YK0g.iv_count (fun x => negb (covered (na ++ lz) x)) e.
Proof. intros na lz e. unfold esec. cbn [map YK0g.sum_count]. rewrite wiv_uw. lia. Qed.
Lemma eager_used_mmap_model : forall (a n : word) md,
YK0g.model_ivs_wf md -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
eager_used (mmap_model a n md) = eager_used md + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(bv_unsigned a, bv_unsigned n)].
Proof.
intros a n md WF Han. pose proof (model_ivs_wf_parts md WF) as (Wm & Wn & Wl). pose proof WF as (_ & _ & _ & Wsp).
assert (WF' : YK0g.model_ivs_wf (mmap_model a n md)).
{ unfold YK0g.model_ivs_wf, mmap_model. mproj. cbn [vm_maps vm_noaccess vm_init_sp].
split; [apply YK0g.ivs_wf_cons; [exact Han | exact Wm] | split; [exact Wn | split; [exact Wl | exact Wsp]]]. }
rewrite (eager_used_sem _ WF'), (eager_used_sem _ WF). unfold mmap_model. mproj. cbn [vm_maps vm_noaccess YK0g.sum_count].
rewrite (esec_single _ _ (a, n)). cbn [fst snd]. lia.
Qed.
Lemma map_remove_mid : forall l1 (e : word * word) l2,
(forall q, In q (l1 ++ l2) -> fst q <> fst e) -> map_remove (l1 ++ e :: l2) (fst e) = l1 ++ l2.
Proof.
intros l1 e l2 H. unfold map_remove. rewrite filter_app. cbn [List.filter]. rewrite bv_eqb_refl. cbn [negb].
assert (G : forall l, (forall q, In q l -> fst q <> fst e) -> List.filter (fun p : word * word => negb (bv_eqb (fst p) (fst e))) l = l).
{ intros l Hl. induction l as [|q l IH]; [reflexivity|]. cbn [List.filter]. destruct (bv_eqb (fst q) (fst e)) eqn:Eq.
- apply bv_eqb_eq in Eq. exfalso. exact (Hl q (or_introl eq_refl) Eq).
- cbn [negb]. rewrite IH by (intros q' Hq'; exact (Hl q' (or_intror Hq'))). reflexivity. }
rewrite !G; [reflexivity | |]; intros q Hq; apply H; apply in_app_iff; auto.
Qed.
Lemma eager_used_munmap : forall (e : word * word) md l1 l2,
amwf md -> vm_maps (m_vmmaps md) = l1 ++ e :: l2 ->
eager_used (munmap_model (fst e) (snd e) md)
= eager_used md - esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(bv_unsigned (fst e), bv_unsigned (snd e))]
/\ vm_maps (m_vmmaps (munmap_model (fst e) (snd e) md)) = l1 ++ l2.
Proof.
intros e md l1 l2 [(W1 & W2 & W3 & PW & Wsp) NE] E.
assert (WF : YK0g.model_ivs_wf md).
{ split; [|split; [|split]]; [intros q Hq; exact (W1 q Hq) | intros q Hq; exact (W2 q Hq) | intros q Hq; exact (W3 q Hq) | exact Wsp]. }
rewrite E in PW. destruct (pairwise_app_mid _ l1 e l2 PW) as [D1 D2].
pose proof (NE e ltac:(rewrite E; apply in_app_iff; right; left; reflexivity)) as NZe.
assert (OTHER : forall q, In q (l1 ++ l2) -> fst q <> fst e /\
(bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst q))).
{ intros q Hq. pose proof (NE q ltac:(rewrite E; apply in_app_iff in Hq as [?|?]; apply in_app_iff; [left|right;right]; assumption)) as NZq.
assert (D : bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst q)).
{ apply in_app_iff in Hq as [Hq|Hq]; [exact (D1 q Hq) | pose proof (D2 q Hq); lia]. }
split; [|exact D]. intros Ef. rewrite Ef in D. lia. }
assert (RM : map_remove (vm_maps (m_vmmaps md)) (fst e) = l1 ++ l2) by (rewrite E; apply map_remove_mid; intros q Hq; exact (proj1 (OTHER q Hq))).
assert (VM' : vm_maps (m_vmmaps (munmap_model (fst e) (snd e) md)) = l1 ++ l2).
{ unfold munmap_model, with_mmap_destroyed, vm_forget_range. mproj. cbn [vm_maps]. exact RM. }
split; [|exact VM'].
assert (WF' : YK0g.model_ivs_wf (munmap_model (fst e) (snd e) md)).
{ pose proof (bv_unsigned_in_range 64 (snd e)) as Rn. unfold bv_modulus in Rn.
unfold YK0g.model_ivs_wf. rewrite VM'. unfold munmap_model, with_mmap_destroyed, vm_forget_range. mproj. cbn [vm_noaccess vm_init_sp].
split; [| split; [|split; [|exact Wsp]]; apply YK0g.maps_subtract_wf; try lia; intros q Hq; [exact (W2 q Hq) | exact (W3 q Hq)]].
intros q Hq. apply W1. rewrite E. apply in_app_iff in Hq as [?|?]; apply in_app_iff; [left|right;right]; assumption. }
rewrite (eager_used_sem _ WF'), (eager_used_sem _ WF), VM', E. rewrite !YK0g.sum_count_app. cbn [YK0g.sum_count].
rewrite (esec_single _ _ e).
assert (EQ : forall l, (forall q, In q l -> In q (l1 ++ l2)) ->
YK0g.sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps (munmap_model (fst e) (snd e) md)) ++ m_vm_lazy (munmap_model (fst e) (snd e) md)) x)) l
= YK0g.sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x)) l).
{ intros l Hl. apply sum_count_ext_in. intros q x Hq Hx. f_equal. apply (cov_munmap (fst e) (snd e) md x WF).
pose proof (OTHER q (Hl q Hq)) as [_ D]. unfold YK0g.B, YK0g.S in Hx. lia. }
rewrite (EQ l1), (EQ l2) by (intros q Hq; apply in_app_iff; auto). lia.
Qed.
Section f.
Variable segs : list Segment.
Lemma ALedger_equiv : forall ly S S' md,
ALedger segs ly S md ->
(forall c, 1 <= c <= 31 -> reg S' c = reg S c) -> sec_extents ly S' = sec_extents ly S ->
prim_committed S' = prim_committed S -> st_nev S' = st_nev S -> st_sec_reserved S' = st_sec_reserved S ->
ALedger segs ly S' md.
Proof.
intros ly S S' md L REG SE PC NEV RES. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (MONO1 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c'))
by (intros c' Hc'; rewrite (REG c' Hc'); lia).
assert (MONO2 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S' c') <= rg_mapped_user (reg S c') /\ rg_mapped_fa (reg S' c') <= rg_mapped_fa (reg S c'))
by (intros c' Hc'; rewrite (REG c' Hc'); lia).
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) by (intros c' Hc'; rewrite (REG c' Hc'); reflexivity).
constructor; rewrite ?SE, ?PC, ?NEV, ?RES; try assumption.
destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|exact P4].
- eapply Forall_impl; [|exact P1]. intros p (A & B & C). split; [exact A|]. split; apply (cut_ok_mono ly S S' MONO1); assumption.
- intros a Ha. rewrite (P3 a Ha). rewrite (prim_hole_at_same ly S S' HOLES a). tauto.
Qed.
Definition cov_same_on_secs (ly : alayout) (S : astate) (md md' : Model) : Prop :=
forall e x, In e (sec_extents ly S) -> fst e <= x < fst e + snd e ->
covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x.
Lemma esec_same_on_secs' : forall ly S md md',
Forall (fun e => 4096 <= snd e < 2 ^ 64) (sec_extents ly S) -> sec_placed ly S -> cov_same_on_secs ly S md md' ->
esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (sec_extents ly S) = esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S).
Proof.
intros ly S md md' SZ [PF _] COV. apply esec_ext; [|exact COV].
apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [H1 H2] & H3). pose proof (proj1 (Forall_forall _ _) SZ e He) as H4. cbn beta in H4.
ceil; unfold kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma esec_same_on_secs : forall U pp cc bb ly S md md',
WfP U pp cc bb S -> sec_placed ly S -> cov_same_on_secs ly S md md' ->
esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (sec_extents ly S) = esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S).
Proof. intros U pp cc bb ly S md md' W PL COV. exact (esec_same_on_secs' ly S md md' (sec_extents_sizes64P U pp cc bb ly S W) PL COV). Qed.
Lemma in_split_pairwise : forall (l1 l2 : list (Z * Z)) e y,
pairwise zdisjoint (l1 ++ l2) -> In e l1 -> In y l2 -> zdisjoint e y.
Proof.
intros l1 l2 e y PW He Hy. induction l1 as [|z t IH]; [destruct He|]. cbn [app pairwise] in PW. destruct PW as [F PW].
destruct He as [<-|He]; [| exact (IH PW He)]. exact (proj1 (Forall_forall _ _) F y ltac:(apply in_app_iff; right; exact Hy)).
Qed.
Lemma cov_same_on_secs_prim : forall ly S md md',
sec_placed ly S ->
(forall x, ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize) ->
covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
cov_same_on_secs ly S md md'.
Proof.
intros ly S md md' [_ PD] COV e x He Hx. apply COV. intros Hp.
assert (INP : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
pose proof (in_split_pairwise _ _ e _ PD He INP) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma cov_same_on_secs_band : forall ly S md md',
sec_placed ly S ->
(forall x, ~ (kLowShadowBeg <= x < kHighMemBeg) ->
covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
cov_same_on_secs ly S md md'.
Proof.
intros ly S md md' [PF _] COV e x He Hx. apply COV. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [H1 H2] & _).
unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma cov_same_on_secs_apart : forall ly S md md' lo len,
Forall (zdisjoint (lo, len)) (sec_extents ly S) ->
(forall x, ~ (lo <= x < lo + len) ->
covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
cov_same_on_secs ly S md md'.
Proof.
intros ly S md md' lo len F COV e x He Hx. apply COV. pose proof (proj1 (Forall_forall _ _) F e He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma ALedger_cov_kept : forall U pp cc bb ly S md md',
WfP U pp cc bb S -> sec_placed ly S -> ALedger segs ly S md ->
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) -> vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) ->
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) -> vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md) ->
vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md) ->
cov_same_on_secs ly S md md' -> eager_used md' <= eager_used md ->
(forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md')) lo n = true) ->
ALedger segs ly S md'.
Proof.
intros U pp cc bb ly S md md' W PL L VM RES LIM MMB ISP COV EG NAF. pose proof (esec_same_on_secs U pp cc bb ly S md md' W PL COV) as ES.
assert (TOP : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by (unfold alloc_top; rewrite ISP; reflexivity).
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15]. constructor; rewrite ?RES, ?LIM, ?VM, ?ES, ?TOP; try assumption; try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
lia.
Qed.
Lemma cov_same_on_secs_Q : forall ly S md md',
layout_ok ly -> sec_placed ly S ->
(forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
cov_same_on_secs ly S md md'.
Proof.
intros ly S md md' LO [_ PD] COV e x He Hx. apply COV. intros Hq.
assert (INQ : In (ly_Q ly, kPtrArrayResv) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
pose proof (in_split_pairwise _ _ e _ PD He INQ) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma ALedger_qcommit' : forall ly S S' md md',
layout_ok ly -> Forall (fun e => 4096 <= snd e < 2 ^ 64) (sec_extents ly S) -> sec_placed ly S -> ALedger segs ly S md ->
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) -> vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) ->
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) -> vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md) ->
vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md) ->
(forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
eager_used md' <= eager_used md + 8 * kPtrArrayEntriesPerCommit ->
(forall c, 1 <= c <= 31 -> reg S' c = reg S c) -> sec_extents ly S' = sec_extents ly S -> prim_committed S' = prim_committed S ->
st_nev S' = st_nev S -> st_sec_reserved S' = st_sec_reserved S + kPtrArrayEntriesPerCommit ->
(forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md')) lo n = true) ->
ALedger segs ly S' md'.
Proof.
intros ly S S' md md' LO W PL L VM RES LIM MMB ISP COV EG REG SE PC NEV SR NAF.
pose proof (esec_same_on_secs' ly S md md' W PL (cov_same_on_secs_Q ly S md md' LO PL COV)) as ES.
assert (TOP : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by (unfold alloc_top; rewrite ISP; reflexivity).
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (MONO1 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c'))
by (intros c' Hc'; rewrite (REG c' Hc'); lia).
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) by (intros c' Hc'; rewrite (REG c' Hc'); reflexivity).
constructor; rewrite ?RES, ?LIM, ?VM, ?SE, ?PC, ?NEV, ?SR, ?ES, ?TOP; try assumption; try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|exact P4].
+ eapply Forall_impl; [|exact P1]. intros p (A & B & C). split; [exact A|]. split; apply (cut_ok_mono ly S S' MONO1); assumption.
+ intros a Ha. rewrite (P3 a Ha). rewrite (prim_hole_at_same ly S S' HOLES a). tauto.
- unfold kPtrArrayEntriesPerCommit in *. lia.
Qed.
Lemma ALedger_qcommit : forall U pp cc bb ly S S' md md',
layout_ok ly -> WfP U pp cc bb S -> sec_placed ly S -> ALedger segs ly S md ->
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) -> vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) ->
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) -> vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md) ->
vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md) ->
(forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
eager_used md' <= eager_used md + 8 * kPtrArrayEntriesPerCommit ->
(forall c, 1 <= c <= 31 -> reg S' c = reg S c) -> sec_extents ly S' = sec_extents ly S -> prim_committed S' = prim_committed S ->
st_nev S' = st_nev S -> st_sec_reserved S' = st_sec_reserved S + kPtrArrayEntriesPerCommit ->
(forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md')) lo n = true) ->
ALedger segs ly S' md'.
Proof.
intros U pp cc bb ly S S' md md' LO W. exact (ALedger_qcommit' ly S S' md md' LO (sec_extents_sizes64P U pp cc bb ly S W)).
Qed.
Lemma anon_grant_facts : forall U pp cc bb ly S md (a n : word),
layout_ok ly -> WfP U pp cc bb S -> sec_placed ly S -> ALedger segs ly S md ->
grant_ok_na_pin md a (bv_unsigned n) = true -> 0 < bv_unsigned n -> bv_unsigned n mod 4096 = 0 ->
page_aligned (bv_unsigned a) /\ in_app (bv_unsigned a) (bv_unsigned n) /\ bv_unsigned a + bv_unsigned n <= ASAN_CEIL /\
Forall (zdisjoint (bv_unsigned a, bv_unsigned n)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps).
Proof.
intros U pp cc bb ly S md a n LO W PL L G Hn Hnal.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
unfold grant_ok_na_pin in G. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. unfold page_size in G1.
assert (Hn64 : Z_to_bv 64 (bv_unsigned n) = n) by (apply w64_uw). rewrite Hn64 in G4.
set (lo := bv_unsigned a) in *. set (len := bv_unsigned n) in *.
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (CE : lo + len <= ASAN_CEIL).
{ unfold ASAN_CEIL. apply (YM05.grant_below_ceil (alloc_top (m_vmmaps md)) (lo + len) L13); [| exact G3].
apply Z.mod_divide in G1 as [q Hq]; [|lia]. apply Z.mod_divide in Hnal as [q' Hq']; [|lia]. rewrite Hq, Hq'.
replace (q * 4096 + q' * 4096) with ((q + q') * 4096) by lia. apply Z_mod_mult. }
ceil.
assert (RF : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 ->
In (wiv z) (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. pose proof (YK13.region_free_In _ a n (w64 (fst z)) (w64 (snd z)) G4 Hin) as D.
unfold w64 in D. rewrite !Z_to_bv_unsigned, !bv_wrap_small in D by (unfold bv_modulus; lia). unfold zdisjoint. cbn [fst snd]. subst lo len. lia. }
assert (RFm : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 -> In (wiv z) (vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. apply RF; [exact Z1 | exact Z2 | exact Z3 | apply in_app_iff; right; exact Hin]. }
assert (BAND : Forall (zdisjoint (lo, len)) band_maps).
{ apply Forall_forall. intros z Hz. apply RFm; [ | | | exact (L11 z Hz)]; unfold band_maps in Hz; cbn in Hz;
destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia. }
assert (APP : in_app lo len).
{ pose proof BAND as B'. unfold band_maps in B'. apply Forall_cons_iff in B' as [D1 B']. apply Forall_cons_iff in B' as [D2 B']. apply Forall_cons_iff in B' as [D3 _].
unfold zdisjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3. unfold in_app.
unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *.
split; [| clear - D1 D2 D3 Hn CE CR0; lia].
apply Z.mod_divide in G1 as [q Hq]; [|lia]. subst lo len. clear - Hq G2. lia. }
split; [exact G1|]. split; [exact APP|]. split; [exact CE|].
pose proof (lo_high ly LO) as [HP1 HP2].
assert (PRIM : zdisjoint (lo, len) (ly_prim ly, kPrimResvSize)).
{ destruct L4 as (pieces & (P1 & P2 & P3) & P4).
unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo (ly_prim ly + kPrimResvSize)) as [X1|X1]; [|right; lia].
destruct (Z_lt_le_dec (ly_prim ly) (lo + len)) as [X2|X2]; [|left; lia]. exfalso.
set (x := Z.max lo (ly_prim ly)).
assert (Hx : ly_prim ly <= x < ly_prim ly + kPrimResvSize) by (subst x; unfold kPrimResvSize in *; lia).
assert (NH : ~ prim_hole_at ly S x).
{ intros (c0 & h & Hc0 & Hh & _). rewrite (wf_noholes U pp cc bb S c0 W Hc0) in Hh. exact Hh. }
apply (P3 x Hx) in NH. apply Exists_exists in NH as (p0 & Hp0 & Hin0). unfold in_zr in Hin0.
pose proof (proj1 (P4 p0) Hp0) as (Hm0 & C1 & C2 & C3).
pose proof (RFm p0 ltac:(unfold kHighMemBeg in HP1; lia) ltac:(lia) ltac:(clear - C2 C3 HP1 HP2 CR CR0; unfold kPrimResvSize, kHighMemBeg, ASAN_CEIL in *; lia) Hm0) as D.
unfold zdisjoint in D. cbn [fst snd] in D. subst x. lia. }
pose proof (lo_stk_ceil ly LO) as STK.
assert (IMG : zdisjoint (lo, len) (ly_img ly)).
{ pose proof (lo_img ly LO) as (J0 & J1 & J2 & J3). unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo (fst (ly_img ly) + snd (ly_img ly))) as [X1|X1]; [|right; lia].
destruct (Z_lt_le_dec (fst (ly_img ly)) (lo + len)) as [X2|X2]; [|left; lia]. exfalso.
set (x := Z.max lo (fst (ly_img ly))).
destruct (L14 x ltac:(unfold in_zr; subst x; lia)) as (e & He & E1).
pose proof (YK13.region_free_In _ a n (fst e) (snd e) G4 ltac:(apply in_app_iff; left; rewrite L3, <- surjective_pairing; exact He)) as D.
subst lo len x. lia. }
assert (PERM : Forall (zdisjoint (lo, len)) (perm_maps ly)).
{ apply Forall_forall. intros z Hz. lazymatch eval cbv in depot_has_trace with
| true => pose proof (perm_facts ly 1 LO ltac:(lia) z Hz) as (Z1 & Z2 & Z3 & _); apply RFm; [lia | lia | lia | exact (L10 z Hz)]
| false =>
(* PROVISIONAL empty-depot branch: an empty NB / SB slot (4096, 0) is disjoint from the grant, which starts at 4096 or above. *)
destruct (perm_maps_cases ly z Hz) as [->|Hl];
[ unfold zdisjoint, in_app in *; cbn [fst snd]; right; lia
| pose proof (perm_facts ly 1 LO ltac:(lia) z Hz) as (Z1 & Z2 & Z3 & _); apply RFm; [lia | lia | lia | exact (L10 z Hl)] ]
end. }
assert (QQ : zdisjoint (lo, len) (ly_Q ly, kPtrArrayResv)).
{ pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [Q1 Q2]. cbn [fst snd] in Q1, Q2.
apply RFm; [cbn [fst]; lia | cbn [snd]; unfold kPtrArrayResv; lia | cbn [fst snd]; unfold kLowShadowBeg, kPtrArrayResv, ASAN_CEIL in *; lia | exact L5]. }
assert (SEC : Forall (zdisjoint (lo, len)) (sec_extents ly S)).
{ apply Forall_forall. intros e He. destruct PL as [PF _]. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [E1 E2] & E3).
pose proof (proj1 (Forall_forall _ _) (sec_extents_sizes64P U pp cc bb ly S W) e He) as E4. cbn beta in E4.
apply RFm; [lia | lia | unfold ASAN_CEIL in *; lia | exact (L7 e He)]. }
rewrite !Forall_app. split; [| split; [exact SEC | split; [exact PERM | exact BAND]]].
unfold static_extents, owned_extents. apply Forall_app. split.
- pose proof PERM as PM. unfold perm_maps in PM. apply Forall_app in PM as [PM _].
apply Forall_cons_iff in PM as [PT PM]. apply Forall_cons_iff in PM as [PFk PM]. apply Forall_cons_iff in PM as [PNB PM].
apply Forall_cons_iff in PM as [PSB PM]. apply Forall_cons_iff in PM as [PC PM]. apply Forall_cons_iff in PM as [PD _].
repeat apply Forall_cons; try apply Forall_nil; try assumption.
unfold zdisjoint in PC |- *. cbn [fst snd] in PC |- *. unfold kCtxMapSize in PC. lia.
- apply Forall_cons; [| apply Forall_cons; [exact IMG | apply Forall_nil]].
unfold zdisjoint. cbn [fst snd]. left. unfold ASAN_CEIL in *. lia.
Qed.
Lemma ALedger_anon : forall U pp cc bb ly S S' md (a n : word) (r : nat) (av : Z),
layout_ok ly -> WfP U pp cc bb S -> sec_placed ly S -> amwf md -> ALedger segs ly S md ->
grant_ok_na_pin md a (bv_unsigned n) = true ->
aregime S   -> 0 < bv_unsigned n <= MALLOC_MAX + 4 * 4096 -> bv_unsigned n mod 4096 = 0 ->
(forall c, 1 <= c <= 31 -> reg S' c = reg S c) -> prim_committed S' = prim_committed S ->
sec_extents (set_ly_sec ly r av) S' = sec_extents ly S ++ [(bv_unsigned a, bv_unsigned n)] ->
st_nev S' = st_nev S + 1 -> st_sec_reserved S' = st_sec_reserved S ->
ALedger segs (set_ly_sec ly r av) S' (mmap_model a n md).
Proof.
intros U pp cc bb ly S S' md a n r av LO W PL MW L G NEV Hn Hal REG PC SE NEV' SR.
pose proof (anon_grant_facts U pp cc bb ly S md a n LO W PL L G ltac:(lia) Hal) as (FA1 & FA2 & FA3 & FA4).
set (md' := mmap_model a n md).
assert (ELZ : lazy_zones (set_ly_sec ly r av) = lazy_zones ly) by reflexivity.
assert (EPM : perm_maps (set_ly_sec ly r av) = perm_maps ly) by reflexivity.
assert (EP : ly_prim (set_ly_sec ly r av) = ly_prim ly) by reflexivity.
assert (EQ : ly_Q (set_ly_sec ly r av) = ly_Q ly) by reflexivity.
assert (EI : ly_img (set_ly_sec ly r av) = ly_img ly) by reflexivity.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
pose proof G as G'. unfold grant_ok_na_pin in G. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3.
assert (Hn64 : Z_to_bv 64 (bv_unsigned n) = n) by (apply w64_uw).
rewrite Hn64 in G4.
assert (RF : forall b s, In (b, s) (vm_maps (m_vmmaps md)) -> bv_unsigned a + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned a).
{ intros b s Hin. apply (YK13.region_free_In _ a n b s G4). apply in_app_iff. right. exact Hin. }
assert (VM' : vm_maps (m_vmmaps md') = (a, n) :: vm_maps (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (RES' : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (LIM' : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (MMB' : vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (ISP' : vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (TOP' : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by (unfold alloc_top; rewrite ISP'; reflexivity).
assert (NA' : vm_noaccess (m_vmmaps md') = vm_noaccess (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (LZ' : m_vm_lazy md' = m_vm_lazy md) by (subst md'; unfold mmap_model; mproj; reflexivity).
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (MWF : YK0g.model_ivs_wf md).
{ destruct MW as [(W1 & W2 & W3 & _) _]. split; [|split; [|split]]; [intros q Hq; exact (W1 q Hq) | intros q Hq; exact (W2 q Hq) | intros q Hq; exact (W3 q Hq) |].
exact (ceil_top_init_sp_ok _ L13). }
assert (EG : eager_used md' = eager_used md + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(bv_unsigned a, bv_unsigned n)]).
{ subst md'. apply eager_used_mmap_model; [exact MWF |]. ceil. unfold ASAN_CEIL in *. lia. }
assert (MONO1 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c'))
by (intros c' Hc'; rewrite (REG c' Hc'); lia).
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) by (intros c' Hc'; rewrite (REG c' Hc'); reflexivity).
constructor; rewrite ?ELZ, ?EPM, ?EP, ?EQ, ?EI, ?VM', ?RES', ?LIM', ?MMB', ?TOP', ?NA', ?LZ', ?SE, ?PC, ?NEV', ?SR, ?EG; try assumption.
-   destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|].
+ eapply Forall_impl; [|exact P1]. intros p (A & B & C). split; [exact A|].
change (cut_ok (set_ly_sec ly r av) S' (fst p) /\ cut_ok (set_ly_sec ly r av) S' (fst p + snd p)) with (cut_ok ly S' (fst p) /\ cut_ok ly S' (fst p + snd p)).
split; apply (cut_ok_mono ly S S' MONO1); assumption.
+ intros x Hx. rewrite (P3 x Hx). change (prim_hole_at (set_ly_sec ly r av) S' x) with (prim_hole_at ly S' x). rewrite (prim_hole_at_same ly S S' HOLES x). tauto.
+ intros p. rewrite (P4 p). split.
* intros (Hin & B1 & B2 & B3). split; [right; exact Hin | auto].
* intros ([Heq|Hin] & B1 & B2 & B3); [| auto]. exfalso.
pose proof (lo_high ly LO) as [HP1 HP2].
assert (Ua : bv_unsigned a = fst p).
{ apply (f_equal fst) in Heq. cbn [fst wiv] in Heq. rewrite Heq. unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
ceil; unfold bv_modulus, kHighMemBeg, kPrimResvSize, ASAN_CEIL in *. lia. }
assert (PRIM : zdisjoint (bv_unsigned a, bv_unsigned n) (ly_prim ly, kPrimResvSize)).
{ exact (proj1 (Forall_forall _ _) FA4 _ ltac:(apply in_app_iff; left; unfold static_extents, owned_extents; cbn; tauto)). }
unfold zdisjoint in PRIM. cbn [fst snd] in PRIM. lia.
-   right. exact L5.
-   right. exact L6.
-   intros e He. apply in_app_iff in He as [He|[<-|[]]]; [right; exact (L7 e He)|]. left. unfold wiv, w64. cbn [fst snd]. rewrite !w64_uw. reflexivity.
-   intros e [<-|He].
+ apply Exists_exists. exists (bv_unsigned a, bv_unsigned n). split; [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity|]. cbn [fst snd]. lia.
+ apply Exists_exists. pose proof (L8 e He) as X. apply Exists_exists in X as (z & Hz & Hz'). exists z. split; [|exact Hz'].
apply in_app_iff in Hz as [Hz|Hz]; apply in_app_iff; [left; exact Hz | right; apply in_app_iff; left; exact Hz].
-   lazymatch eval cbv in depot_has_trace with true => idtac | false => nb_same ly end. rewrite esec_app. lia.
-   intros z Hz. right. exact (L10 z Hz).
-   intros z Hz. right. exact (L11 z Hz).
-   intros e z He Hz. apply in_app_iff in He as [He|[<-|[]]]; [exact (L12 e z He Hz)|].
exact (proj1 (Forall_forall _ _) FA4 z ltac:(rewrite !in_app_iff; right; right; left; exact Hz)).
Qed.
Lemma ALedger_munmap : forall U pp cc bb ly S S' md (e : Z * Z) E1 E2,
layout_ok ly -> WfP U pp cc bb S -> sec_placed ly S -> amwf md -> ALedger segs ly S md ->
sec_extents ly S = E1 ++ e :: E2 -> sec_extents ly S' = E1 ++ E2 ->
(forall c, 1 <= c <= 31 -> reg S' c = reg S c) -> prim_committed S' = prim_committed S ->
st_nev S' = st_nev S -> st_sec_reserved S' = st_sec_reserved S ->
let md' := munmap_model (w64 (fst e)) (w64 (snd e)) md in
ALedger segs ly S' md' /\
(exists M1 M2, vm_maps (m_vmmaps md) = M1 ++ wiv e :: M2 /\ vm_maps (m_vmmaps md') = M1 ++ M2) /\
eager_used md' = eager_used md - esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [e].
Proof.
intros U pp cc bb ly S S' md e E1 E2 LO W PL MW L ES ES' REG PC NEV SR md'.
destruct PL as [PF PD]. pose proof (sec_extents_sizes64P U pp cc bb ly S W) as SZ.
assert (He : In e (sec_extents ly S)) by (rewrite ES; apply in_app_iff; right; left; reflexivity).
pose proof (proj1 (Forall_forall _ _) PF e He) as (EA & [EH1 EH2] & EC). pose proof (proj1 (Forall_forall _ _) SZ e He) as ESZ. cbn beta in ESZ.
pose proof alloc_ceiling_val as CV. pose proof (lo_high ly LO) as HI. pose proof (lo_extra ly LO) as (_ & XF & XD).
assert (UE1 : bv_unsigned (w64 (fst e)) = fst e) by (unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | ceil; unfold bv_modulus, kHighMemBeg, ASAN_CEIL in *; lia]).
assert (UE2 : bv_unsigned (w64 (snd e)) = snd e) by (unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus in *; lia]).
assert (WINJ : forall z, 0 <= fst z < 2 ^ 64 -> 0 <= snd z < 2 ^ 64 -> wiv z = wiv e -> z = e).
{ intros z B1 B2 Heq. pose proof (f_equal (fun q => bv_unsigned (fst q)) Heq) as X1. pose proof (f_equal (fun q => bv_unsigned (snd q)) Heq) as X2.
cbn [fst snd wiv] in X1, X2. rewrite UE1 in X1. rewrite UE2 in X2. unfold w64 in X1, X2.
rewrite Z_to_bv_unsigned, bv_wrap_small in X1 by (unfold bv_modulus; lia). rewrite Z_to_bv_unsigned, bv_wrap_small in X2 by (unfold bv_modulus; lia).
destruct z; cbn [fst snd] in *; subst; destruct e; reflexivity. }
assert (APART : forall e', In e' (E1 ++ E2) -> zdisjoint e' e).
{ intros e' He'. rewrite ES, <- app_assoc in PD. cbn [app] in PD. destruct (pairwise_app_mid zdisjoint E1 e (E2 ++ static_extents ly) PD) as [D1 D2].
apply in_app_iff in He' as [He'|He']; [exact (D1 e' He')|]. pose proof (D2 e' ltac:(apply in_app_iff; left; exact He')) as D. unfold zdisjoint in *. lia. }
assert (STAT : forall y, In y (static_extents ly) -> zdisjoint e y).
{ intros y Hy. rewrite ES, <- app_assoc in PD. cbn [app] in PD. destruct (pairwise_app_mid zdisjoint E1 e (E2 ++ static_extents ly) PD) as [_ D2].
exact (D2 y ltac:(apply in_app_iff; right; exact Hy)). }
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
destruct (in_split _ _ (L7 e He)) as (M1 & M2 & EM).
destruct (eager_used_munmap (wiv e) md M1 M2 MW EM) as [EG VM']. cbn [fst snd wiv] in EG, VM'. rewrite UE1, UE2 in EG.
replace (fst e, snd e) with e in EG by (destruct e; reflexivity). fold md' in EG, VM'.
destruct MW as [(W1 & W2 & W3 & PW & _) NE].
assert (MWF : YK0g.model_ivs_wf md).
{ split; [|split; [|split]]; [intros q Hq; exact (W1 q Hq) | intros q Hq; exact (W2 q Hq) | intros q Hq; exact (W3 q Hq) | exact (ceil_top_init_sp_ok _ L13)]. }
assert (SURV : forall x, In x (vm_maps (m_vmmaps md)) -> x <> wiv e -> In x (M1 ++ M2)).
{ intros x Hx Hne. rewrite EM in Hx. apply in_app_iff in Hx as [Hx|[Hx|Hx]]; [apply in_app_iff; left; exact Hx | exfalso; exact (Hne (eq_sym Hx)) | apply in_app_iff; right; exact Hx]. }
assert (RES' : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)) by (subst md'; unfold munmap_model, with_mmap_destroyed, vm_forget_range; mproj; reflexivity).
assert (LIM' : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)) by (subst md'; unfold munmap_model, with_mmap_destroyed, vm_forget_range; mproj; reflexivity).
assert (MMB' : vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md)) by (subst md'; unfold munmap_model, with_mmap_destroyed, vm_forget_range; mproj; reflexivity).
assert (ISP' : vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md)) by (subst md'; unfold munmap_model, with_mmap_destroyed, vm_forget_range; mproj; reflexivity).
assert (TOP' : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by (unfold alloc_top; rewrite ISP'; reflexivity).
assert (ESX : esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (E1 ++ E2) = esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (E1 ++ E2)).
{ apply esec_ext.
- apply Forall_forall. intros e' He'. assert (In e' (sec_extents ly S)) as Hin by (rewrite ES; apply in_app_iff in He' as [?|?]; apply in_app_iff; [left|right;right]; assumption).
pose proof (proj1 (Forall_forall _ _) PF e' Hin) as (_ & [H1 H2] & H3). pose proof (proj1 (Forall_forall _ _) SZ e' Hin) as H4. cbn beta in H4.
ceil; unfold kHighMemBeg, ASAN_CEIL in *. lia.
- intros e' x He' Hx. subst md'. rewrite (cov_munmap (w64 (fst e)) (w64 (snd e)) md x MWF); [reflexivity|]. rewrite UE1, UE2.
pose proof (APART e' He') as D. unfold zdisjoint in D. lia. }
assert (MONO1 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c'))
by (intros c' Hc'; rewrite (REG c' Hc'); lia).
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) by (intros c' Hc'; rewrite (REG c' Hc'); reflexivity).
split; [| split; [exists M1, M2; split; [exact EM | exact VM'] | exact EG]].
constructor; rewrite ?VM', ?RES', ?LIM', ?MMB', ?TOP', ?ES', ?PC, ?NEV, ?SR, ?ESX, ?EG; try assumption;
try (destruct L15 as [N1 N2];
assert (NAS : vm_noaccess (m_vmmaps md') = maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned (w64 (fst e))) (bv_unsigned (w64 (fst e)) + bv_unsigned (w64 (snd e))))
by (subst md'; destruct md as [fd0 [maps0 lz0 mt0] io0 fs0 proc0 lim0 tm0]; reflexivity);
rewrite NAS; split; apply region_free_subtract; first [exact W2 | assumption]).
-   destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|].
+ eapply Forall_impl; [|exact P1]. intros p (A & B & C). split; [exact A|]. split; apply (cut_ok_mono ly S S' MONO1); assumption.
+ intros x Hx. rewrite (P3 x Hx). rewrite (prim_hole_at_same ly S S' HOLES x). tauto.
+ intros p. rewrite (P4 p). split.
* intros (Hin & B1 & B2 & B3). split; [|auto]. apply SURV; [exact Hin|]. intros Heq.
destruct HI as [HP1 HP2].
pose proof (WINJ p ltac:(ceil; unfold kHighMemBeg, kPrimResvSize, ASAN_CEIL in *; lia) ltac:(ceil; unfold kHighMemBeg, kPrimResvSize, ASAN_CEIL in *; lia) Heq) as ->.
pose proof (STAT (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
* intros (Hin & B1 & B2 & B3). split; [|auto]. rewrite EM. apply in_app_iff in Hin as [?|?]; apply in_app_iff; [left|right;right]; assumption.
-   apply SURV; [exact L5|]. intros Heq.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [HQ1 HQ2]. cbn [fst snd] in HQ1, HQ2.
pose proof (WINJ (ly_Q ly, kPtrArrayResv) ltac:(cbn; ceil; clear - HQ1 HQ2 CR CR0; unfold kLowShadowBeg, kHighMemBeg, kPtrArrayResv, ASAN_CEIL in *; lia) ltac:(cbn; unfold kPtrArrayResv; lia) Heq) as X.
pose proof (STAT (ly_Q ly, kPtrArrayResv) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D. rewrite <- X in D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kPtrArrayResv in D. lia.
-   apply SURV; [exact L6|]. intros Heq.
pose proof (WINJ (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg) ltac:(cbn; unfold kHighShadowBeg, kHighShadowEnd; lia) ltac:(cbn; unfold kHighShadowBeg, kHighShadowEnd; lia) Heq) as X.
apply (f_equal fst) in X. cbn [fst] in X. clear - X EH1 EH2 ESZ. unfold kHighShadowBeg, kHighMemBeg, kLowShadowBeg in *. lia.
-   intros e' He'. assert (Hin : In e' (sec_extents ly S)) by (rewrite ES; apply in_app_iff in He' as [?|?]; apply in_app_iff; [left|right;right]; assumption).
apply SURV; [exact (L7 e' Hin)|]. intros Heq.
pose proof (proj1 (Forall_forall _ _) PF e' Hin) as (_ & [H1 H2] & H3). pose proof (proj1 (Forall_forall _ _) SZ e' Hin) as H4. cbn beta in H4.
pose proof (WINJ e' ltac:(ceil; unfold kHighMemBeg, ASAN_CEIL in *; lia) ltac:(lia) Heq) as ->. pose proof (APART e He') as D. unfold zdisjoint in D. lia.
-   intros q Hq. assert (Hq0 : In q (vm_maps (m_vmmaps md))) by (rewrite EM; apply in_app_iff in Hq as [?|?]; apply in_app_iff; [left|right;right]; assumption).
pose proof (L8 q Hq0) as X. apply Exists_exists in X as (z & Hz & Hqz). apply Exists_exists. exists z. split; [|exact Hqz].
rewrite ES in Hz. apply in_app_iff in Hz as [Hz|Hz]; [apply in_app_iff; left; exact Hz|]. apply in_app_iff. right.
apply in_app_iff in Hz as [Hz|[<-|Hz]]; [apply in_app_iff; left; exact Hz | exfalso | apply in_app_iff; right; exact Hz].
rewrite EM in PW. destruct (pairwise_app_mid _ M1 (wiv e) M2 PW) as [D1 D2]. cbn [fst snd wiv] in D1, D2. rewrite UE1, UE2 in D1, D2.
pose proof (NE q Hq0) as NZq. apply in_app_iff in Hq as [Hq|Hq]; [pose proof (D1 q Hq) | pose proof (D2 q Hq)]; lia.
-   rewrite ES in L9. rewrite esec_app, esec_cons in L9. rewrite esec_app, esec_cons, esec_nil. lia.
-   intros z Hz. apply SURV; [exact (L10 z Hz)|]. intros Heq. lazymatch eval cbv in depot_has_trace with
| true => pose proof (perm_facts ly 1 LO ltac:(lia) z Hz) as (Z1 & Z2 & Z3 & _);
  pose proof (WINJ z ltac:(lia) ltac:(lia) Heq) as ->; pose proof (L12 e e He Hz) as D; unfold zdisjoint in D; lia
| false => pose proof (perm_live_sub ly z Hz) as Hzp; pose proof (perm_facts ly 1 LO ltac:(lia) z Hzp) as (Z1 & Z2 & Z3 & _);
  pose proof (WINJ z ltac:(lia) ltac:(lia) Heq) as ->; pose proof (L12 e e He Hzp) as D; unfold zdisjoint in D; lia
end.
-   intros z Hz. apply SURV; [exact (L11 z Hz)|]. intros Heq.
pose proof (STAT (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(unfold static_extents; apply in_app_iff; right; left; reflexivity)) as D0.
unfold band_maps in Hz. cbn in Hz.
destruct Hz as [<-|[<-|[<-|[]]]];
(unshelve epose proof (WINJ _ _ _ Heq) as X;
[cbn; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia | cbn; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia |];
apply (f_equal fst) in X; cbn [fst] in X;
clear - X EH1 EH2 ESZ; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
-   intros e' z He' Hz. apply L12; [|exact Hz]. rewrite ES. apply in_app_iff in He' as [?|?]; apply in_app_iff; [left|right;right]; assumption.
Qed.
End f.
End d.
