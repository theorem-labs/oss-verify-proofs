(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QMow QoSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qcrs QUcd QCUT QMow QoSL.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Fixpoint ro_bytes_b (A : Z) (bs : list byte) : bool :=
match bs with
| [] => true
| b :: bs' =>
match seg_rom segs (wa A) with
| Some b' => bv_eqb b b' && ro_addr segs (wa A) && ro_bytes_b (A + 1) bs'
| None => false
end
end.

Lemma ro_bytes_b_sound : forall bs A, ro_bytes_b A bs = true -> ro_bytes segs A bs.
Proof.
induction bs as [|b bs IH]; intros A H; cbn in *; [exact I|].
destruct (seg_rom segs (wa A)) as [b'|] eqn:E; [|discriminate].
apply andb_prop in H. destruct H as [H1 H3]. apply andb_prop in H1. destruct H1 as [H1 H2].
unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
split; [split; [exact E| exact H2]|]. apply IH. exact H3.
Qed.

Lemma ro_cells_image : forall m A bs,
mem_inv segs m -> ro_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
ro_cells segs m A [CB (length bs) bs].
Proof.
intros m A bs Hinv Hb HA Hl. split.
- cbn. split; [reflexivity|exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; try assumption.
apply ro_bytes_b_sound. exact Hb.
Qed.

Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
match n with
| O => Some []
| S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
| Some b, Some bs => Some (b :: bs)
| _, _ => None
end
end.

End WithSegs.

End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi Qqcs Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import QQIi Qqcs.
Import Qcrs QUcd QCUT.
Import Qsn5.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma u64_range : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. exact H. Qed.

Lemma in_wivs_covered : forall z l, in_wivs z l = covered l z.
Proof.
intros z l. unfold in_wivs, covered. induction l as [|iv l IH]; cbn; [reflexivity|].
rewrite IH. f_equal.
Qed.

Lemma covered_true : forall l y, covered l y = true <->
exists iv, In iv l /\ bv_unsigned (fst iv) <= y < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
intros l y. unfold covered. rewrite existsb_exists. unfold in_iv, in_rng, B, Qqcs.S.
split.
- intros (iv & Hin & Hb). exists iv. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. auto.
- intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma covered_false : forall l y, covered l y = false <->
forall iv, In iv l -> y < bv_unsigned (fst iv) \/ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= y.
Proof.
intros l y. split.
- intros H iv Hin. destruct (Z.lt_ge_cases y (bv_unsigned (fst iv))); [left; lia|].
destruct (Z.lt_ge_cases y (bv_unsigned (fst iv) + bv_unsigned (snd iv))); [|right; lia].
exfalso. assert (covered l y = true) by (apply covered_true; exists iv; auto). congruence.
- intros H. destruct (covered l y) eqn:E; [|reflexivity]. exfalso.
apply covered_true in E as (iv & Hin & H1 & H2). destruct (H iv Hin); lia.
Qed.

Lemma in_zivs_app : forall y l1 l2, in_zivs y (l1 ++ l2) = in_zivs y l1 || in_zivs y l2.
Proof. intros. unfold in_zivs. apply existsb_app. Qed.

Lemma in_zivs_map_wiv2z : forall y l, in_zivs y (map wiv2z l) = covered l y.
Proof.
intros y l. rewrite <- in_wivs_covered. unfold in_zivs, in_wivs. induction l as [|iv l IH]; cbn; [reflexivity|].
rewrite IH. reflexivity.
Qed.

Lemma covered_cons : forall a n l y,
covered ((a, n) :: l) y = in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n) y || covered l y.
Proof. reflexivity. Qed.

Lemma in_rng_true : forall lo hi y, in_rng lo hi y = true <-> lo <= y < hi.
Proof.
intros. unfold in_rng. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma in_rng_false : forall lo hi y, in_rng lo hi y = false <-> (y < lo \/ hi <= y).
Proof.
intros. unfold in_rng. rewrite andb_false_iff, Z.leb_gt, Z.ltb_ge. tauto.
Qed.

Lemma covered_map_remove : forall l (a n : word) y,
(forall e, In e l -> fst e = a -> snd e = n) ->
region_free (map_remove l a) a n = true ->
0 < bv_unsigned n ->
covered (map_remove l a) y = covered l y && negb (in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n) y).
Proof.
intros l a n y Hsz Hfree Hn.
destruct (in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n) y) eqn:Ey.
- apply in_rng_true in Ey. rewrite andb_false_r. apply covered_false. intros iv Hin.
pose proof (region_free_In _ _ _ (fst iv) (snd iv) Hfree ltac:(rewrite <- surjective_pairing; exact Hin)) as Ho.
unfold iv_overlap in Ho. apply andb_false_iff in Ho as [Ho|Ho]; apply Z.ltb_ge in Ho; lia.
- rewrite andb_true_r. apply in_rng_false in Ey.
destruct (covered l y) eqn:El.
+ apply covered_true in El as (iv & Hin & H1 & H2). apply covered_true. exists iv. split; [|lia].
unfold map_remove. apply filter_In. split; [exact Hin|]. cbn.
destruct (bv_eqb (fst iv) a) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E.
pose proof (Hsz iv Hin E) as Hs. rewrite E in H1. rewrite E, Hs in H2. lia.
+ apply covered_false. intros iv Hin. apply (proj1 (covered_false l y) El). unfold map_remove in Hin. apply filter_In in Hin as [Hin _]. exact Hin.
Qed.

Lemma zin_true : forall z iv, zin z iv = true <-> fst iv <= z < snd iv.
Proof. intros. unfold zin. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma in_zivs_true : forall z l, in_zivs z l = true <-> exists iv, In iv l /\ fst iv <= z < snd iv.
Proof.
intros z l. unfold in_zivs. rewrite existsb_exists. split; intros (iv & H1 & H2); exists iv; split; auto; apply zin_true; auto.
Qed.

Lemma covered_filter_sub : forall f l y, covered (List.filter f l) y = true -> covered l y = true.
Proof.
intros f l y H. apply covered_true in H as (iv & Hin & Hr). apply filter_In in Hin as [Hin _].
apply covered_true. exists iv. auto.
Qed.

Section Cov.
Variable L : lvp.

Definition emaps (mo : Model) : list (word * word) :=
List.filter (fun e => negb (excl_entry L e)) (vm_maps (m_vmmaps mo)).
Definition ecov (mo : Model) (y : Z) : bool := covered (emaps mo) y.
Definition bcov (y : Z) : bool := in_zivs y (lv_base L).

Definition appcov (mo : Model) (y : Z) : bool := bcov y || ecov mo y.

Lemma appvis_cov : forall mo y, in_zivs y (appvis L mo) = appcov mo y.
Proof. intros mo y. unfold appvis, appcov, bcov, ecov, emaps. rewrite in_zivs_app, in_zivs_map_wiv2z. reflexivity. Qed.

Lemma shz_mono : forall y y', y <= y' -> shz L y <= shz L y'.
Proof. intros. unfold shz. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.

Lemma sh_iv_iff : forall lo hi t, lo < hi ->
(shz L lo <= t < shz L (hi - 1) + 1 <-> exists y, lo <= y < hi /\ shz L y = t).
Proof.
intros lo hi t Hlh. split.
- intros [H1 H2]. unfold shz in *.
set (y0 := 8 * (t - lv_shoff L)).
exists (Z.max lo y0). split; [| ].
+ split; [lia|]. assert (y0 <= 8 * ((hi - 1) / 8)) by (unfold y0; lia).
pose proof (Z.mul_div_le (hi - 1) 8 ltac:(lia)). lia.
+ destruct (Z.le_gt_cases lo y0).
* rewrite Z.max_r by lia. unfold y0. rewrite Z.mul_comm, Z.div_mul by lia. lia.
* rewrite Z.max_l by lia.
assert (lo / 8 = t - lv_shoff L); [|lia].
symmetry. apply (Z.div_unique lo 8 (t - lv_shoff L) (lo - y0)); unfold y0 in *; [left|]; lia.
- intros (y & Hy & <-). split; [apply shz_mono; lia|]. pose proof (shz_mono y (hi - 1) ltac:(lia)). lia.
Qed.

Lemma shivs_sem : forall mo z,
in_zivs z (shivs L mo) = true <-> exists y, appcov mo y = true /\ shz L y = z.
Proof.
intros mo z. unfold shivs. rewrite in_zivs_true. split.
- intros (iv & Hin & Hz). apply in_map_iff in Hin as (iv0 & <- & Hin). apply filter_In in Hin as [Hin Hne].
unfold nonempty in Hne. apply Z.ltb_lt in Hne. unfold sh_iv in Hz. cbn [fst snd] in Hz.
destruct (proj1 (sh_iv_iff _ _ _ Hne) Hz) as (y & Hy & Hs).
exists y. split; [|exact Hs]. rewrite <- appvis_cov. apply in_zivs_true. exists iv0. auto.
- intros (y & Hc & Hs). rewrite <- appvis_cov in Hc. apply in_zivs_true in Hc as (iv0 & Hin & Hy).
exists (sh_iv L iv0). split.
+ apply in_map_iff. exists iv0. split; [reflexivity|]. apply filter_In. split; [exact Hin|]. unfold nonempty. apply Z.ltb_lt. lia.
+ unfold sh_iv. cbn [fst snd]. apply (proj2 (sh_iv_iff (fst iv0) (snd iv0) z ltac:(lia))). exists y. auto.
Qed.

Lemma allowed_byte_iff : forall mo z,
allowed_byte L mo z = true <-> appcov mo z = true \/ exists y, appcov mo y = true /\ shz L y = z.
Proof.
intros mo z. unfold allowed_byte. rewrite orb_true_iff, appvis_cov, shivs_sem. tauto.
Qed.

Lemma hidden_iff : forall mo a,
hidden L mo a = true <-> appcov mo (bv_unsigned a) = false /\ forall y, appcov mo y = true -> shz L y <> bv_unsigned a.
Proof.
intros mo a. unfold hidden. rewrite negb_true_iff. split.
- intros H. split.
+ destruct (appcov mo (bv_unsigned a)) eqn:E; [|reflexivity]. exfalso.
assert (allowed_byte L mo (bv_unsigned a) = true) by (apply allowed_byte_iff; left; exact E). congruence.
+ intros y Hy Hs. assert (allowed_byte L mo (bv_unsigned a) = true) by (apply allowed_byte_iff; right; exists y; auto). congruence.
- intros [H1 H2]. destruct (allowed_byte L mo (bv_unsigned a)) eqn:E; [|reflexivity]. exfalso.
apply allowed_byte_iff in E as [E|(y & Hy & Hs)]; [congruence| exact (H2 y Hy Hs)].
Qed.

Lemma visible_iff : forall mo a,
hidden L mo a = false <-> appcov mo (bv_unsigned a) = true \/ exists y, appcov mo y = true /\ shz L y = bv_unsigned a.
Proof.
intros mo a. unfold hidden. rewrite negb_false_iff. apply allowed_byte_iff.
Qed.

Lemma G_iff : forall mo p,
G L mo p = true <-> aligned p = true /\ exists z, allowed_byte L mo z = true /\ bv_unsigned p <= z < bv_unsigned p + 4096.
Proof.
intros mo p. unfold G. rewrite andb_true_iff, orb_true_iff, !existsb_exists. split.
- intros [Hal Hor]. split; [exact Hal|].
assert (Hm : forall iv, page_meets p iv = true -> exists z, zin z iv = true /\ bv_unsigned p <= z < bv_unsigned p + 4096).
{ intros iv Hpm. unfold page_meets in Hpm. apply andb_prop in Hpm as [Hpm H3]. apply andb_prop in Hpm as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
exists (Z.max (fst iv) (bv_unsigned p)). split; [apply zin_true; lia| lia]. }
destruct Hor as [(iv & Hin & Hpm)|(iv & Hin & Hpm)]; destruct (Hm iv Hpm) as (z & Hz & Hr); exists z; (split; [|exact Hr]);
unfold allowed_byte; apply orb_true_iff; [left|right]; unfold in_zivs; apply existsb_exists; exists iv; auto.
- intros [Hal (z & Hz & Hr)]. split; [exact Hal|].
assert (Hm : forall iv, zin z iv = true -> page_meets p iv = true).
{ intros iv Hzi. apply zin_true in Hzi. unfold page_meets.
apply andb_true_intro; split; [apply andb_true_intro; split|]; apply Z.ltb_lt; lia. }
unfold allowed_byte in Hz. apply orb_prop in Hz as [Hz|Hz]; unfold in_zivs in Hz; apply existsb_exists in Hz as (iv & Hin & Hzi);
[left|right]; exists iv; auto.
Qed.

Definition excl_inside (mo : Model) : Prop :=
forall e, In e (vm_maps (m_vmmaps mo)) -> excl_entry L e = true ->
exists x, In x (lv_excl L) /\ fst x <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= snd x.

Definition excl_mapped (mo : Model) : Prop :=
forall x y, In x (lv_excl L) -> fst x <= y < snd x -> covered (vm_maps (m_vmmaps mo)) y = true.

Lemma excl_entry_true : forall e, excl_entry L e = true <->
exists x, In x (lv_excl L) /\ 0 < bv_unsigned (snd e) /\ fst x < snd x /\
bv_unsigned (fst e) < snd x /\ fst x < bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
intros e. unfold excl_entry. rewrite existsb_exists. unfold zoverlap, wiv2z. cbn [fst snd].
pose proof (u64_range (snd e)).
split; intros (x & Hin & H'); exists x; (split; [exact Hin|]).
- apply andb_prop in H' as [H' H4]. apply andb_prop in H' as [H' H3]. apply andb_prop in H' as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4. lia.
- repeat (apply andb_true_intro; split); apply Z.ltb_lt; lia.
Qed.

Lemma excl_entry_false : forall e, excl_entry L e = false <->
forall x, In x (lv_excl L) -> fst x < snd x -> 0 < bv_unsigned (snd e) ->
snd x <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst x.
Proof.
intros e. split.
- intros H x Hx Hne Hsz. destruct (Z.lt_ge_cases (bv_unsigned (fst e)) (snd x)); [|left; lia].
destruct (Z.lt_ge_cases (fst x) (bv_unsigned (fst e) + bv_unsigned (snd e))); [|right; lia].
exfalso. assert (excl_entry L e = true) by (apply excl_entry_true; exists x; repeat split; auto). congruence.
- intros H. destruct (excl_entry L e) eqn:E; [|reflexivity]. exfalso. apply excl_entry_true in E as (x & Hx & H0 & H1 & H2 & H3).
destruct (H x Hx H1 H0); lia.
Qed.

Lemma fresh_not_excl : forall mo (a n : word),
excl_mapped mo -> 0 < bv_unsigned n ->
region_free (vm_maps (m_vmmaps mo)) a n = true ->
excl_entry L (a, n) = false.
Proof.
intros mo a n Hem Hn Hfree. apply excl_entry_false. cbn [fst snd]. intros x Hx Hne _.
destruct (Z.le_gt_cases (snd x) (bv_unsigned a)); [left; lia|].
destruct (Z.le_gt_cases (bv_unsigned a + bv_unsigned n) (fst x)); [right; lia|]. exfalso.

set (y := Z.max (bv_unsigned a) (fst x)).
assert (Hy : fst x <= y < snd x /\ bv_unsigned a <= y < bv_unsigned a + bv_unsigned n) by (unfold y; lia).
destruct Hy as [Hy1 Hy2]. pose proof (Hem x y Hx Hy1) as Hc. apply covered_true in Hc as (iv & Hin & Hr).
pose proof (region_free_In _ _ _ (fst iv) (snd iv) Hfree ltac:(rewrite <- surjective_pairing; exact Hin)) as Ho.
unfold iv_overlap in Ho. apply andb_false_iff in Ho as [Ho|Ho]; apply Z.ltb_ge in Ho; lia.
Qed.

Lemma ecov_cons : forall (a n : word) l y,
excl_entry L (a, n) = false ->
covered (List.filter (fun e => negb (excl_entry L e)) ((a, n) :: l)) y
= in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n) y || covered (List.filter (fun e => negb (excl_entry L e)) l) y.
Proof. intros a n l y He. cbn [List.filter]. rewrite He. cbn [negb]. apply covered_cons. Qed.

Lemma filter_map_remove : forall l a,
List.filter (fun e => negb (excl_entry L e)) (map_remove l a) = map_remove (List.filter (fun e => negb (excl_entry L e)) l) a.
Proof.
intros l a. unfold map_remove. induction l as [|e l IH]; cbn; [reflexivity|].
destruct (negb (bv_eqb (fst e) a)) eqn:E1; destruct (negb (excl_entry L e)) eqn:E2; cbn; rewrite ?E1, ?E2, IH; reflexivity.
Qed.

Definition h_add (h : VmMaps) (a n : word) : VmMaps :=
mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition h_destroy (h : VmMaps) (a n : word) : VmMaps :=
mkVmMapsFull (vm_reserved h)
(maps_subtract (vm_maps h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition h_munmap (h : VmMaps) (a n : word) : VmMaps :=
mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
(maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition grant_model (mo : Model) (a n : word) : Model := with_vmmaps (h_add (m_vmmaps mo) a n) mo.

Definition commit_model (mo : Model) (a n : word) : Model :=
vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
(with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) a n) mo).

Definition destroy_model (mo : Model) (a n : word) : Model :=
with_mmap_destroyed a n (h_destroy (m_vmmaps mo) a n) mo.

Definition remap_model (mo : Model) (a n : word) : Model := vm_add_lazy a n (commit_model mo a n).

Definition munmap_model (mo : Model) (a n : word) : Model :=
vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps (h_munmap (m_vmmaps mo) a n) mo).

Lemma maps_grant : forall mo a n, vm_maps (m_vmmaps (grant_model mo a n)) = (a, n) :: vm_maps (m_vmmaps mo).
Proof. reflexivity. Qed.
Lemma maps_commit : forall mo a n, vm_maps (m_vmmaps (commit_model mo a n)) = vm_maps (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.

Lemma maps_remap : forall mo a n, vm_maps (m_vmmaps (remap_model mo a n)) = vm_maps (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma maps_munmap : forall mo a n, vm_maps (m_vmmaps (munmap_model mo a n)) = map_remove (vm_maps (m_vmmaps mo)) a.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.

Lemma mat_grant : forall mo a n, m_vm_materialized (grant_model mo a n) = m_vm_materialized mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma mat_commit : forall mo a n, m_vm_materialized (commit_model mo a n)
= List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.

Lemma mat_remap : forall mo a n, m_vm_materialized (remap_model mo a n)
= List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma mat_munmap : forall mo a n, m_vm_materialized (munmap_model mo a n)
= List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.

Lemma limit_grant : forall mo a n, vm_limit (m_vmmaps (grant_model mo a n)) = vm_limit (m_vmmaps mo).
Proof. reflexivity. Qed.
Lemma limit_commit : forall mo a n, vm_limit (m_vmmaps (commit_model mo a n)) = vm_limit (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.

Lemma limit_remap : forall mo a n, vm_limit (m_vmmaps (remap_model mo a n)) = vm_limit (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma limit_munmap : forall mo a n, vm_limit (m_vmmaps (munmap_model mo a n)) = vm_limit (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.

Definition vm_onlyA (mo mo' : Model) : Prop :=
m_fd mo' = m_fd mo /\ m_io mo' = m_io mo /\ m_fsys mo' = m_fsys mo /\ m_proc mo' = m_proc mo /\
m_lim mo' = m_lim mo /\ m_time mo' = m_time mo.

Lemma vm_onlyA_facts : forall mo mo', vm_onlyA mo mo' ->
m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo /\ m_tid mo' = m_tid mo /\ m_stdin mo' = m_stdin mo.
Proof.
intros mo mo' (H1 & H2 & H3 & H4 & _). unfold m_fds, m_fs, m_halted, m_tid, m_stdin. rewrite H1, H2, H3, H4. repeat split; reflexivity.
Qed.

Lemma vm_onlyA_grant : forall mo a n, vm_onlyA mo (grant_model mo a n).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. repeat split; reflexivity. Qed.
Lemma vm_onlyA_commit : forall mo a n, vm_onlyA mo (commit_model mo a n).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. repeat split; reflexivity. Qed.

Lemma vm_onlyA_remap : forall mo a n, vm_onlyA mo (remap_model mo a n).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. repeat split; reflexivity. Qed.
Lemma vm_onlyA_munmap : forall mo a n, vm_onlyA mo (munmap_model mo a n).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. repeat split; reflexivity. Qed.

Lemma msim_grant : forall mo mo' a n, msim mo mo' -> msim (grant_model mo a n) (grant_model mo' a n).
Proof.
intros mo mo' a n H. unfold grant_model. pose proof (msim_facts L _ _ H) as (_ & _ & _ & _ & _ & Hv & _). rewrite Hv.
apply msim_with_vmmaps. exact H.
Qed.
Lemma msim_commit : forall mo mo' a n, msim mo mo' -> msim (commit_model mo a n) (commit_model mo' a n).
Proof.
intros mo mo' a n H. unfold commit_model. pose proof (msim_facts L _ _ H) as (_ & _ & _ & _ & _ & Hv & _). rewrite Hv.
apply (msim_vm_forget_range L). apply msim_with_vmmaps. exact H.
Qed.

Lemma msim_remap : forall mo mo' a n, msim mo mo' -> msim (remap_model mo a n) (remap_model mo' a n).
Proof. intros mo mo' a n H. unfold remap_model. apply (msim_vm_add_lazy L). apply msim_commit. exact H. Qed.
Lemma msim_munmap : forall mo mo' a n, msim mo mo' -> msim (munmap_model mo a n) (munmap_model mo' a n).
Proof.
intros mo mo' a n H. unfold munmap_model. pose proof (msim_facts L _ _ H) as (_ & _ & _ & _ & _ & Hv & _). rewrite Hv.
apply (msim_vm_forget_range L). apply msim_with_vmmaps. exact H.
Qed.

Definition inR (a n : word) (y : Z) : bool := in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n) y.

Lemma appcov_grant : forall mo a n y, excl_entry L (a, n) = false ->
appcov (grant_model mo a n) y = inR a n y || appcov mo y.
Proof.
intros mo a n y He. unfold appcov, ecov, emaps. rewrite maps_grant, (ecov_cons a n _ y He). unfold inR.
destruct (in_rng _ _ y), (bcov y), (covered _ y); reflexivity.
Qed.

Lemma appcov_munmap : forall mo a n y,
(forall e, In e (vm_maps (m_vmmaps mo)) -> fst e = a -> snd e = n) ->
region_free (map_remove (vm_maps (m_vmmaps mo)) a) a n = true -> 0 < bv_unsigned n ->
appcov (munmap_model mo a n) y = bcov y || (ecov mo y && negb (inR a n y)).
Proof.
intros mo a n y Hsz Hfree Hn. unfold appcov, ecov, emaps. rewrite maps_munmap, filter_map_remove.
rewrite (covered_map_remove _ a n y); [reflexivity| | |exact Hn].
- intros e He. apply filter_In in He as [He _]. apply Hsz. exact He.
- apply region_free_intro. intros b s Hin. eapply region_free_In; [exact Hfree|].
unfold map_remove in *. apply filter_In in Hin as [Hin Hb]. apply filter_In in Hin as [Hin _]. apply filter_In. auto.
Qed.

Lemma allowed_grow : forall mo mo' (a n : word),
(forall y, appcov mo' y = inR a n y || appcov mo y) -> 0 < bv_unsigned n ->
forall z, allowed_byte L mo' z = allowed_byte L mo z || inR a n z || zin z (sh_iv L (wiv2z (a, n))).
Proof.
intros mo mo' a n Hc Hn z. unfold wiv2z. cbn [fst snd].
destruct (allowed_byte L mo' z) eqn:E'.
- apply allowed_byte_iff in E' as [E'|(y & Hy & Hs)].
+ rewrite Hc in E'. apply orb_prop in E' as [->|E']; [rewrite orb_true_r; reflexivity|].
rewrite (proj2 (allowed_byte_iff mo z)) by (left; exact E'). reflexivity.
+ rewrite Hc in Hy. apply orb_prop in Hy as [Hy|Hy].
* unfold inR in Hy. apply in_rng_true in Hy.
replace (zin z (sh_iv L (bv_unsigned a, bv_unsigned a + bv_unsigned n))) with true; [rewrite !orb_true_r; reflexivity|].
symmetry. apply zin_true. unfold sh_iv. cbn [fst snd]. apply (proj2 (sh_iv_iff (bv_unsigned a) (bv_unsigned a + bv_unsigned n) z ltac:(lia))). exists y. auto.
* rewrite (proj2 (allowed_byte_iff mo z)) by (right; exists y; auto). reflexivity.
- symmetry. apply orb_false_iff. split; [apply orb_false_iff; split|].
+ destruct (allowed_byte L mo z) eqn:E; [|reflexivity]. exfalso.
apply allowed_byte_iff in E as [E|(y & Hy & Hs)].
* assert (allowed_byte L mo' z = true) by (apply allowed_byte_iff; left; rewrite Hc, E; apply orb_true_r). congruence.
* assert (allowed_byte L mo' z = true) by (apply allowed_byte_iff; right; exists y; rewrite Hc, Hy, orb_true_r; auto). congruence.
+ destruct (inR a n z) eqn:E; [|reflexivity]. exfalso.
assert (allowed_byte L mo' z = true) by (apply allowed_byte_iff; left; rewrite Hc, E; reflexivity). congruence.
+ destruct (zin z _) eqn:E; [|reflexivity]. exfalso. apply zin_true in E. unfold sh_iv in E. cbn [fst snd] in E.
destruct (proj1 (sh_iv_iff (bv_unsigned a) (bv_unsigned a + bv_unsigned n) z ltac:(lia)) E) as (y & Hy & Hs).
assert (allowed_byte L mo' z = true); [|congruence]. apply allowed_byte_iff. right. exists y. split; [|exact Hs].
rewrite Hc. unfold inR. rewrite (proj2 (in_rng_true _ _ y)) by lia. reflexivity.
Qed.

Lemma allowed_shrink : forall mo mo',
(forall y, appcov mo' y = true -> appcov mo y = true) ->
forall z, allowed_byte L mo' z = true -> allowed_byte L mo z = true.
Proof.
intros mo mo' Hc z Hz. apply allowed_byte_iff in Hz as [Hz|(y & Hy & Hs)]; apply allowed_byte_iff.
- left. apply Hc. exact Hz.
- right. exists y. split; [apply Hc; exact Hy| exact Hs].
Qed.

Lemma allowed_lost : forall mo mo' (a n : word),
(forall y, appcov mo' y = bcov y || (ecov mo y && negb (inR a n y))) -> 0 < bv_unsigned n ->
forall z, allowed_byte L mo z = true -> allowed_byte L mo' z = false ->
inR a n z = true \/ zin z (sh_iv L (wiv2z (a, n))) = true.
Proof.
intros mo mo' a n Hc Hn z Hz Hz'.
assert (Hkeep : forall y, appcov mo y = true -> inR a n y = false -> appcov mo' y = true).
{ intros y Hy Hr. rewrite Hc. unfold appcov in Hy. apply orb_prop in Hy as [->|Hy]; [reflexivity|]. rewrite Hy, Hr. apply orb_true_r. }
apply allowed_byte_iff in Hz as [Hz|(y & Hy & Hs)].
- left. destruct (inR a n z) eqn:E; [reflexivity|]. exfalso.
assert (allowed_byte L mo' z = true) by (apply allowed_byte_iff; left; apply Hkeep; assumption). congruence.
- destruct (inR a n y) eqn:E.
+ right. apply zin_true. unfold sh_iv, wiv2z. cbn [fst snd]. unfold inR in E. apply in_rng_true in E.
apply (proj2 (sh_iv_iff (bv_unsigned a) (bv_unsigned a + bv_unsigned n) z ltac:(lia))). exists y. auto.
+ exfalso. assert (allowed_byte L mo' z = true) by (apply allowed_byte_iff; right; exists y; split; [apply Hkeep; assumption| exact Hs]). congruence.
Qed.

Lemma appcov_shrink_of : forall mo mo' (a n : word),
(forall y, appcov mo' y = bcov y || (ecov mo y && negb (inR a n y))) ->
forall y, appcov mo' y = true -> appcov mo y = true.
Proof.
intros mo mo' a n Hc y Hy. rewrite Hc in Hy. unfold appcov. apply orb_prop in Hy as [->|Hy]; [reflexivity|].
apply andb_prop in Hy as [-> _]. apply orb_true_r.
Qed.

Lemma G_grow : forall mo mo' (a n : word),
(forall z, allowed_byte L mo' z = allowed_byte L mo z || inR a n z || zin z (sh_iv L (wiv2z (a, n)))) ->
forall p, G L mo' p = true ->
G L mo p = true \/ In p (pages_meeting (wiv2z (a, n)) ++ pages_meeting (sh_iv L (wiv2z (a, n)))).
Proof.
intros mo mo' a n Ha p HG. apply G_iff in HG as (Hal & z & Hz & Hr). rewrite Ha in Hz.
apply orb_prop in Hz as [Hz|Hz]; [apply orb_prop in Hz as [Hz|Hz]|].
- left. apply G_iff. split; [exact Hal|]. exists z. auto.
- right. apply in_or_app. left. unfold inR in Hz. apply in_rng_true in Hz. unfold wiv2z. cbn [fst snd]. apply pages_meeting_In; [exact Hal| lia| lia].
- right. apply in_or_app. right. apply zin_true in Hz. destruct (sh_iv L (wiv2z (a, n))) as [lo hi]. cbn [fst snd] in Hz. apply pages_meeting_In; [exact Hal| lia| lia].
Qed.

Lemma G_shrink : forall mo mo',
(forall z, allowed_byte L mo' z = true -> allowed_byte L mo z = true) ->
forall p, G L mo' p = true -> G L mo p = true.
Proof.
intros mo mo' Ha p HG. apply G_iff in HG as (Hal & z & Hz & Hr). apply G_iff. split; [exact Hal|]. exists z. auto.
Qed.

Lemma Rsv_grow : forall mo mo' (New : list word),
(forall p, G L mo' p = true -> G L mo p = true \/ In p New) ->
m_vm_materialized mo' = m_vm_materialized mo ->
Rsv L mo' <= Rsv L mo + 4096 * Z.of_nat (length New).
Proof.
intros mo mo' New HG Hm. unfold Rsv.
assert (Hlen : (length (unmat L mo') <= length (unmat L mo ++ New))%nat).
{ apply NoDup_incl_length; [apply unmat_NoDup|]. intros p Hp. apply unmat_In in Hp as [HGp Hmp].
rewrite Hm in Hmp. apply in_or_app. destruct (HG p HGp) as [H|H]; [left; apply unmat_In; auto| right; exact H]. }
rewrite length_app in Hlen. lia.
Qed.

Lemma Rsv_filter : forall mo mo' f,
(forall p, G L mo' p = true -> G L mo p = true) ->
m_vm_materialized mo' = List.filter f (m_vm_materialized mo) ->
Rsv L mo' <= Rsv L mo + 4096 * (Z.of_nat (length (m_vm_materialized mo)) - Z.of_nat (length (m_vm_materialized mo'))).
Proof.
intros mo mo' f HG Hm. unfold Rsv.
assert (Hlen : (length (unmat L mo') <= length (unmat L mo ++ List.filter (fun p => negb (f p)) (m_vm_materialized mo)))%nat).
{ apply NoDup_incl_length; [apply unmat_NoDup|]. intros p Hp. apply unmat_In in Hp as [HGp Hmp]. rewrite Hm in Hmp.
apply in_or_app. destruct (in_dec (weq_dec) p (m_vm_materialized mo)) as [Hin|Hnin].
- right. apply filter_In. split; [exact Hin|]. destruct (f p) eqn:E; [|reflexivity]. exfalso. apply Hmp. apply filter_In. auto.
- left. apply unmat_In. auto. }
rewrite length_app in Hlen.
pose proof (filter_length f (m_vm_materialized mo)) as Hsplit. rewrite Hm. lia.
Qed.

Lemma lazy_grant : forall mo a n, m_vm_lazy (grant_model mo a n) = m_vm_lazy mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma noacc_grant : forall mo a n, vm_noaccess (m_vmmaps (grant_model mo a n)) = vm_noaccess (m_vmmaps mo).
Proof. reflexivity. Qed.

Lemma wf_grant : forall mo a n, model_ivs_wf mo -> bv_unsigned a + bv_unsigned n <= 2^64 -> model_ivs_wf (grant_model mo a n).
Proof.
intros mo a n W Hb. pose proof W as (Wm & Wn & Wl & Wsp). unfold grant_model. apply model_ivs_wf_with_vmmaps; [exact W| |exact Wn|reflexivity].
cbn. apply ivs_wf_cons; [exact Hb| exact Wm].
Qed.

Lemma wf_commit : forall mo a n, model_ivs_wf mo -> model_ivs_wf (commit_model mo a n).
Proof.
intros mo a n W. pose proof W as (Wm & Wn & Wl & Wsp). unfold commit_model. pose proof (u64_range n).
apply model_ivs_wf_vm_forget_range; [lia|]. apply model_ivs_wf_with_vmmaps; [exact W| exact Wm| |reflexivity].
cbn. apply maps_subtract_wf; [exact Wn| lia].
Qed.

Lemma wf_remap : forall mo a n, model_ivs_wf mo -> bv_unsigned a + bv_unsigned n <= 2^64 -> model_ivs_wf (remap_model mo a n).
Proof. intros mo a n W Hb. unfold remap_model. apply model_ivs_wf_vm_add_lazy; [exact Hb| apply wf_commit; exact W]. Qed.

Lemma wf_munmap : forall mo a n, model_ivs_wf mo -> model_ivs_wf (munmap_model mo a n).
Proof.
intros mo a n W. pose proof W as (Wm & Wn & Wl & Wsp). unfold munmap_model. pose proof (u64_range n).
apply model_ivs_wf_vm_forget_range; [lia|]. apply model_ivs_wf_with_vmmaps; [exact W| | |reflexivity]; cbn.
- unfold map_remove. apply ivs_wf_filter. exact Wm.
- apply maps_subtract_wf; [exact Wn| lia].
Qed.

Lemma excl_inside_grant : forall mo a n, excl_inside mo -> excl_entry L (a, n) = false -> excl_inside (grant_model mo a n).
Proof.
intros mo a n Hx He e Hin HE. rewrite maps_grant in Hin. destruct Hin as [<-|Hin]; [congruence|]. exact (Hx e Hin HE).
Qed.
Lemma excl_inside_commit : forall mo a n, excl_inside mo -> excl_inside (commit_model mo a n).
Proof. intros mo a n Hx e Hin HE. rewrite maps_commit in Hin. exact (Hx e Hin HE). Qed.
Lemma excl_inside_remap : forall mo a n, excl_inside mo -> excl_inside (remap_model mo a n).
Proof. intros mo a n Hx e Hin HE. rewrite maps_remap in Hin. exact (Hx e Hin HE). Qed.
Lemma excl_inside_munmap : forall mo a n, excl_inside mo -> excl_inside (munmap_model mo a n).
Proof. intros mo a n Hx e Hin HE. rewrite maps_munmap in Hin. unfold map_remove in Hin. apply filter_In in Hin as [Hin _]. exact (Hx e Hin HE). Qed.

Lemma sum_count_filter_le : forall (P P' : Z -> bool) (f : word * word -> bool) l,
(forall e, In e l -> f e = true -> iv_count P' e = iv_count P e) ->
sum_count P' (List.filter f l) <= sum_count P l.
Proof.
intros P P' f l H. induction l as [|e l IH]; cbn [List.filter sum_count]; [lia|].
assert (IH' := IH ltac:(intros e' He'; apply H; right; exact He')).
pose proof (zcount_nonneg P (B e) (Z.to_nat (Qqcs.S e))) as Hnn.
pose proof (H e (or_introl eq_refl)) as He.
destruct (f e) eqn:Ef; cbn [sum_count].
- rewrite (He eq_refl). unfold iv_count in *. lia.
- unfold iv_count in *. lia.
Qed.

Lemma page_size_4096 : page_size = 4096. Proof. reflexivity. Qed.

Lemma backing_grant : forall mo a n, model_ivs_wf mo -> bv_unsigned a + bv_unsigned n <= 2^64 ->
vm_backing_used (grant_model mo a n) <= vm_backing_used mo + bv_unsigned n.
Proof.
intros mo a n W Hb. rewrite (vm_backing_used_sem _ (wf_grant mo a n W Hb)), (vm_backing_used_sem _ W).
rewrite maps_grant, noacc_grant, lazy_grant, mat_grant. cbn [sum_count].
pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (B (a, n)) (Z.to_nat (Qqcs.S (a, n)))).
unfold iv_count. unfold Qqcs.S in *. cbn [snd] in *. pose proof (u64_range n). rewrite Z2Nat.id in H by lia. lia.
Qed.

Lemma backing_commit : forall mo a n, model_ivs_wf mo ->
vm_backing_used (commit_model mo a n)
+ 4096 * (Z.of_nat (length (m_vm_materialized mo)) - Z.of_nat (length (m_vm_materialized (commit_model mo a n))))
<= vm_backing_used mo + overlap_sum (vm_maps (m_vmmaps mo)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
intros mo a n W. pose proof W as (Wm & Wn & Wl & Wsp). pose proof (u64_range n) as Hn.
set (lo := bv_unsigned a). set (hi := bv_unsigned a + bv_unsigned n).
rewrite (vm_backing_used_sem _ (wf_commit mo a n W)), (vm_backing_used_sem _ W).
rewrite maps_commit, mat_commit.
replace (vm_noaccess (m_vmmaps (commit_model mo a n))) with (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi)
by (destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity).
replace (m_vm_lazy (commit_model mo a n)) with (maps_subtract (m_vm_lazy mo) lo hi)
by (destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity).
destruct (maps_subtract_sem _ lo hi Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem _ lo hi Wl ltac:(lia)) as (_ & _ & Cl).
unfold overlap_sum.
assert (Hs : sum_count (fun x => negb (covered (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi ++ maps_subtract (m_vm_lazy mo) lo hi) x)) (vm_maps (m_vmmaps mo))
<= sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (vm_maps (m_vmmaps mo))
+ sum_count (in_rng lo hi) (vm_maps (m_vmmaps mo))).
{ eapply Z.le_trans.
- apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x) || in_rng lo hi x)).
intros x. rewrite !covered_app, Cn, Cl.
destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng lo hi x); cbn; congruence.
- apply sum_count_or_le. }
unfold lo, hi in *. rewrite page_size_4096. lia.
Qed.

Lemma backing_remap : forall mo a n, model_ivs_wf mo ->
bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2^64 ->
vm_backing_used (remap_model mo a n)
+ 4096 * (Z.of_nat (length (m_vm_materialized mo)) - Z.of_nat (length (m_vm_materialized (remap_model mo a n))))
<= vm_backing_used mo.
Proof.
intros mo a n W Hal Hnl Hpos Hb. pose proof W as (Wm & Wn & Wl & Wsp).
set (lo := bv_unsigned a). set (hi := bv_unsigned a + bv_unsigned n).
rewrite (vm_backing_used_sem _ (wf_remap mo a n W Hb)), (vm_backing_used_sem _ W).
rewrite maps_remap, mat_remap.
replace (vm_noaccess (m_vmmaps (remap_model mo a n))) with (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi)
by (destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity).
replace (m_vm_lazy (remap_model mo a n)) with (lazy_interior a n ++ maps_subtract (m_vm_lazy mo) lo hi)
by (destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity).
rewrite (lazy_interior_aligned a n Hal Hnl Hpos Hb).
destruct (maps_subtract_sem _ lo hi Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem _ lo hi Wl ltac:(lia)) as (_ & _ & Cl).
fold lo. fold hi.
assert (Hs : sum_count (fun x => negb (covered (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi ++ [(a, n)] ++ maps_subtract (m_vm_lazy mo) lo hi) x)) (vm_maps (m_vmmaps mo))
<= sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (vm_maps (m_vmmaps mo))).
{ apply sum_count_mono. intros x. unfold lo, hi in *. rewrite !covered_app, Cn, Cl.
replace (covered [(a, n)] x) with (in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n) x || false) by reflexivity.
destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n) x); cbn; congruence. }
cbn [app] in Hs |- *. unfold lo, hi in *. rewrite page_size_4096. lia.
Qed.

Lemma backing_munmap : forall mo a n, model_ivs_wf mo ->
region_free (map_remove (vm_maps (m_vmmaps mo)) a) a n = true ->
vm_backing_used (munmap_model mo a n)
+ 4096 * (Z.of_nat (length (m_vm_materialized mo)) - Z.of_nat (length (m_vm_materialized (munmap_model mo a n))))
<= vm_backing_used mo.
Proof.
intros mo a n W Hfree. pose proof W as (Wm & Wn & Wl & Wsp). pose proof (u64_range n) as Hn.
set (lo := bv_unsigned a). set (hi := bv_unsigned a + bv_unsigned n).
rewrite (vm_backing_used_sem _ (wf_munmap mo a n W)), (vm_backing_used_sem _ W).
rewrite maps_munmap, mat_munmap.
replace (vm_noaccess (m_vmmaps (munmap_model mo a n))) with (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi)
by (destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity).
replace (m_vm_lazy (munmap_model mo a n)) with (maps_subtract (m_vm_lazy mo) lo hi)
by (destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity).
destruct (maps_subtract_sem _ lo hi Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem _ lo hi Wl ltac:(lia)) as (_ & _ & Cl).
fold lo. fold hi.

assert (Hs : sum_count (fun x => negb (covered (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi ++ maps_subtract (m_vm_lazy mo) lo hi) x)) (map_remove (vm_maps (m_vmmaps mo)) a)
<= sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (vm_maps (m_vmmaps mo))).
{ unfold map_remove. apply sum_count_filter_le. intros [b s] Hin Hb.
unfold iv_count. apply zcount_ext. intros x Hx. rewrite !covered_app, Cn, Cl.
pose proof (region_free_In _ _ _ b s Hfree ltac:(unfold map_remove; apply filter_In; split; [exact Hin| exact Hb])) as Ho.
unfold iv_overlap in Ho. unfold B, Qqcs.S in Hx. cbn [fst snd] in Hx.
pose proof (u64_range s). rewrite Z2Nat.id in Hx by lia.
assert (Hr : in_rng lo hi x = false).
{ apply in_rng_false. apply andb_false_iff in Ho as [Ho|Ho]; apply Z.ltb_ge in Ho; unfold lo, hi; lia. }
rewrite Hr. destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x); reflexivity. }
unfold lo, hi in *. rewrite page_size_4096. lia.
Qed.

Lemma Phi_grant : forall mo a n, model_ivs_wf mo -> excl_entry L (a, n) = false ->
0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2^64 ->
Phi L (grant_model mo a n)
<= Phi L mo + bv_unsigned n
+ 4096 * Z.of_nat (length (pages_meeting (wiv2z (a, n)) ++ pages_meeting (sh_iv L (wiv2z (a, n))))).
Proof.
intros mo a n W He Hn Hb. unfold Phi.
pose proof (backing_grant mo a n W Hb).
pose proof (Rsv_grow mo (grant_model mo a n) _ (G_grow mo _ a n (allowed_grow mo _ a n (fun y => appcov_grant mo a n y He) Hn)) (mat_grant mo a n)).
lia.
Qed.

Lemma Phi_commit : forall mo a n, model_ivs_wf mo ->
Phi L (commit_model mo a n) <= Phi L mo + overlap_sum (vm_maps (m_vmmaps mo)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
intros mo a n W. unfold Phi.
pose proof (backing_commit mo a n W).
assert (HG : forall p, G L (commit_model mo a n) p = true -> G L mo p = true).
{ intros p. rewrite (G_maps L mo (commit_model mo a n)); [auto|]. apply maps_commit. }
pose proof (Rsv_filter mo (commit_model mo a n) _ HG (mat_commit mo a n)). lia.
Qed.

Lemma Phi_remap : forall mo a n, model_ivs_wf mo ->
bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2^64 ->
Phi L (remap_model mo a n) <= Phi L mo.
Proof.
intros mo a n W Hal Hnl Hpos Hb. unfold Phi.
pose proof (backing_remap mo a n W Hal Hnl Hpos Hb).
assert (HG : forall p, G L (remap_model mo a n) p = true -> G L mo p = true).
{ intros p. rewrite (G_maps L mo (remap_model mo a n)); [auto|]. apply maps_remap. }
pose proof (Rsv_filter mo (remap_model mo a n) _ HG (mat_remap mo a n)). lia.
Qed.

Lemma Phi_munmap : forall mo a n, model_ivs_wf mo ->
(forall e, In e (vm_maps (m_vmmaps mo)) -> fst e = a -> snd e = n) ->
region_free (map_remove (vm_maps (m_vmmaps mo)) a) a n = true -> 0 < bv_unsigned n ->
Phi L (munmap_model mo a n) <= Phi L mo.
Proof.
intros mo a n W Hsz Hfree Hn. unfold Phi.
pose proof (backing_munmap mo a n W Hfree).
assert (HG : forall p, G L (munmap_model mo a n) p = true -> G L mo p = true).
{ apply G_shrink. apply allowed_shrink. eapply appcov_shrink_of. intros y. apply appcov_munmap; assumption. }
pose proof (Rsv_filter mo (munmap_model mo a n) _ HG (mat_munmap mo a n)). lia.
Qed.

Lemma length_pages_meeting_aligned : forall lo hi,
lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
Z.of_nat (length (pages_meeting (lo, hi))) = (hi - lo) / 4096.
Proof.
intros lo hi Hl Hh Hle. unfold pages_meeting. rewrite length_pages_in.
cbn [fst snd]. rewrite (pagedown_of_aligned lo Hl), (pageup_of_aligned hi Hh), (pagedown_of_aligned _ Hh), (pageup_of_aligned _ Hl).
pose proof (Z.div_pos (hi - lo) 4096 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma length_pages_meeting_le : forall lo hi, lo <= hi ->
Z.of_nat (length (pages_meeting (lo, hi))) <= (hi - lo) / 4096 + 2.
Proof.
intros lo hi Hle. unfold pages_meeting. rewrite length_pages_in. cbn [fst snd].
pose proof (pagedown_le lo) as (A1 & A2 & A3). pose proof (pageup_ge hi) as (B1 & B2 & B3).
rewrite (pageup_of_aligned _ A3), (pagedown_of_aligned _ B3).
destruct (mod0_multiple _ A3) as [ql El]. destruct (mod0_multiple _ B3) as [qh Eh]. rewrite El, Eh in *.
replace (4096 * qh - 4096 * ql) with ((qh - ql) * 4096) by lia. rewrite Z.div_mul by lia.
pose proof (Z.div_mod (hi - lo) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (hi - lo) 4096 ltac:(lia)). lia.
Qed.

Lemma sh_iv_len : forall lo hi, lo mod 8 = 0 -> hi mod 8 = 0 -> lo < hi ->
snd (sh_iv L (lo, hi)) - fst (sh_iv L (lo, hi)) = (hi - lo) / 8.
Proof.
intros lo hi Hl Hh Hlt. unfold sh_iv, shz. cbn [fst snd].
pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod hi 8 ltac:(lia)).
rewrite Hl in *. rewrite Hh in *. set (ql := lo / 8) in *. set (qh := hi / 8) in *.
replace (hi - 1) with (8 * (qh - 1) + 7) by lia. rewrite Z.mul_comm, Z.div_add_l by lia. change (7 / 8) with 0.
replace (hi - lo) with ((qh - ql) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

End Cov.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Definition areg (ms : machine_state) (r : bv 5) : word := reg_get (ms_regs ms) r.
Lemma in_a0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = areg ms 10.
Proof. reflexivity. Qed.
Lemma in_a1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = areg ms 11.
Proof. reflexivity. Qed.
Lemma in_a2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = areg ms 12.
Proof. reflexivity. Qed.
Lemma in_a3_si : forall segs ms x8, in_arg (sys_input segs ms x8) 3 = areg ms 13.
Proof. reflexivity. Qed.
Lemma in_a4_si : forall segs ms x8, in_arg (sys_input segs ms x8) 4 = areg ms 14.
Proof. reflexivity. Qed.
Lemma in_a5_si : forall segs ms x8, in_arg (sys_input segs ms x8) 5 = areg ms 15.
Proof. reflexivity. Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_si : forall segs ms x8, in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

Definition bytes_in (mp : word -> option byte) (a : Z) (bs : list byte) : Prop :=
0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\
forall i, (i < length bs)%nat -> mp (wa (a + Z.of_nat i)) = nth_error bs i.

Lemma ms_read_byte_mrd : forall segs ms a,
ms_rom ms = seg_rom segs -> ms_read_byte ms a = mrd segs (ms_mem ms) a.
Proof. intros segs ms a H. unfold ms_read_byte, mrd. rewrite H. reflexivity. Qed.

Lemma bytes_at_in : forall segs ms a bs,
ms_rom ms = seg_rom segs -> bytes_at segs (ms_mem ms) a bs -> bytes_in (ms_read_byte ms) a bs.
Proof.
intros segs ms a bs Hrom (Ha & Hl & H). split; [lia|]. split; [lia|].
intros i Hi. rewrite (ms_read_byte_mrd segs) by exact Hrom. apply H. exact Hi.
Qed.

Lemma bytes_in_app : forall mp a bs1 bs2,
bytes_in mp a (bs1 ++ bs2) <-> bytes_in mp a bs1 /\ bytes_in mp (a + Z.of_nat (length bs1)) bs2.
Proof.
intros mp a bs1 bs2. unfold bytes_in. rewrite length_app. split.
- intros (Ha & Hl & H). repeat split; try lia.
+ intros i Hi. rewrite (H i) by lia. rewrite nth_error_app1 by lia. reflexivity.
+ intros i Hi. replace (a + Z.of_nat (length bs1) + Z.of_nat i) with (a + Z.of_nat (length bs1 + i)) by lia.
rewrite (H (length bs1 + i)%nat) by lia. rewrite nth_error_app2 by lia. f_equal. lia.
- intros ((Ha & Hl1 & H1) & (Ha2 & Hl2 & H2)). repeat split; try lia.
intros i Hi. destruct (Nat.ltb_spec0 i (length bs1)).
+ rewrite nth_error_app1 by lia. apply H1. lia.
+ rewrite nth_error_app2 by lia. rewrite <- (H2 (i - length bs1)%nat) by lia. f_equal. f_equal. lia.
Qed.

Lemma bytes_in_cons : forall mp a b bs,
bytes_in mp a (b :: bs) -> mp (wa a) = Some b /\ bytes_in mp (a + 1) bs.
Proof.
intros mp a b bs H. change (b :: bs) with ([b] ++ bs) in H. apply bytes_in_app in H as [H1 H2].
split; [|exact H2]. destruct H1 as (_ & _ & H1). specialize (H1 0%nat ltac:(cbn; lia)).
rewrite Z.add_0_r in H1. exact H1.
Qed.

Lemma read_bytes_aux_bytes_in : forall bs mp a,
bytes_in mp a bs -> read_bytes_aux mp (wa a) (length bs) = Some bs.
Proof.
induction bs as [|b bs IH]; intros mp a H; [reflexivity|].
apply bytes_in_cons in H as [Hb H]. cbn [read_bytes_aux length]. rewrite Hb.
rewrite wa_succ, (IH _ _ H). reflexivity.
Qed.

Lemma word_to_nat_of_nat : forall n, Z.of_nat n < 2^64 -> word_to_nat (Z_to_bv 64 (Z.of_nat n)) = n.
Proof. intros. unfold word_to_nat. rewrite unsigned_lit by lia. lia. Qed.

Lemma read_bytes_map_bytes_in : forall bs mp a,
bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
read_bytes_map mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = Some bs.
Proof.
intros bs mp a H Hl. rewrite read_bytes_map_eq. rewrite word_to_nat_of_nat by exact Hl.
apply read_bytes_aux_bytes_in, H.
Qed.

Lemma readable_bytes_bytes_in : forall bs mp a,
bytes_in mp a bs -> Z.of_nat (length bs) < 2^64 ->
readable_bytes mp (wa a) (Z_to_bv 64 (Z.of_nat (length bs))) = bs.
Proof.
intros. apply readable_bytes_full, read_bytes_map_bytes_in; assumption.
Qed.

Lemma read_cstr_aux_bytes_in : forall str fuel mp a,
(length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
bytes_in mp a (str ++ [Z_to_bv 8 0]) ->
read_cstr_aux mp (wa a) fuel = CstrOk str.
Proof.
induction str as [|b str IH]; intros fuel mp a Hf Hnz H.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. apply bytes_in_cons in H as [Hb _].
cbn [read_cstr_aux]. rewrite Hb. reflexivity.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. apply bytes_in_cons in H as [Hb H].
cbn [read_cstr_aux]. rewrite Hb.
assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
{ destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
rewrite Hne, wa_succ. rewrite (IH fuel mp (a + 1)); [reflexivity| cbn in Hf; lia | |exact H].
intro Hin. apply Hnz. right. exact Hin.
Qed.

Lemma read_cstr_aux_toolong_bytes_in : forall fuel str mp a,
(fuel <= length str)%nat -> ~ In (Z_to_bv 8 0) str ->
bytes_in mp a str ->
read_cstr_aux mp (wa a) fuel = CstrTooLong.
Proof.
induction fuel as [|fuel IH]; intros str mp a Hf Hnz H; [reflexivity|].
destruct str as [|b str]; [cbn in Hf; lia|]. apply bytes_in_cons in H as [Hb H].
cbn [read_cstr_aux]. rewrite Hb.
assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
{ destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
rewrite Hne, wa_succ. rewrite (IH str mp (a + 1)); [reflexivity| cbn in Hf; lia | |exact H].
intro Hin. apply Hnz. right. exact Hin.
Qed.

Definition iovec_bytes (iovs : list (word * word)) : list byte :=
flat_map (fun p => le8 (fst p) ++ le8 (snd p)) iovs.

Lemma length_iovec_bytes : forall iovs, length (iovec_bytes iovs) = (16 * length iovs)%nat.
Proof.
induction iovs as [|[b l] iovs IH]; [reflexivity|]. cbn [iovec_bytes flat_map fst snd].
rewrite !length_app, !length_le8. unfold iovec_bytes in IH. rewrite IH. cbn [length]. lia.
Qed.

Lemma read_u64_bytes_in : forall mp a v,
bytes_in mp a (le8 v) -> read_u64 mp (wa a) = Some v.
Proof.
intros mp a v H. unfold read_u64.
pose proof (read_bytes_map_bytes_in _ _ _ H ltac:(rewrite length_le8; cbn; lia)) as R. rewrite length_le8 in R.
change (Z.of_nat 8) with 8 in R. rewrite R. rewrite le_bytes_to_word_le8. reflexivity.
Qed.

Lemma wa_add : forall a (k : word), (wa a + k)%bv = wa (a + bv_unsigned k).
Proof. intros. rewrite <- (Z_to_bv_bv_unsigned k) at 1. unfold wa. apply lit_add_lit. Qed.

Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^63 /\ bytes_in mp (bv_unsigned (fst iov)) bs.

Lemma wa_unsigned_id : forall w : word, wa (bv_unsigned w) = w.
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

Lemma copy_iovecs_aux_bytes_in : forall iovs bufs mp a,
bytes_in mp a (iovec_bytes iovs) -> Forall2 (iov_ok mp) iovs bufs ->
copy_iovecs_aux mp (wa a) (length iovs) = ImpOk iovs.
Proof.
intros iovs bufs mp a H HF. revert a H. induction HF as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; intros a H; [reflexivity|].
cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
rewrite !length_le8 in H2. rewrite !length_le8 in H3.
cbn [copy_iovecs_aux length]. unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
rewrite !wa_add. change (bv_unsigned (8%bv : word)) with 8. change (bv_unsigned (16%bv : word)) with 16.
replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
cbn [fst snd] in Hl. subst l. rewrite unsigned_lit by lia.
replace (2 ^ 63 <=? Z.of_nat (length bs)) with false by (symmetry; apply Z.leb_gt; lia).
replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
unfold iovec_bytes in IH. rewrite (IH _ H3). reflexivity.
Qed.

Lemma copy_iovecs_accesses_bytes_in : forall iovs bufs mp a,
bytes_in mp a (iovec_bytes iovs) -> Forall2 (iov_ok mp) iovs bufs ->
copy_iovecs_accesses mp (wa a) (length iovs) = map (fun k => (wa (a + 16 * Z.of_nat k), 16%nat)) (seq 0 (length iovs)).
Proof.
intros iovs bufs mp a H HF. revert a H. induction HF as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; intros a H; [reflexivity|].
cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
rewrite !length_le8 in H2. rewrite !length_le8 in H3.
cbn [copy_iovecs_accesses length seq map]. unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
rewrite !wa_add. change (bv_unsigned (8%bv : word)) with 8. change (bv_unsigned (16%bv : word)) with 16.
replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
cbn [fst snd] in Hl. subst l. rewrite unsigned_lit by lia.
replace (2 ^ 63 <=? Z.of_nat (length bs)) with false by (symmetry; apply Z.leb_gt; lia).
replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
unfold iovec_bytes in IH. rewrite (IH _ H3). rewrite <- seq_shift, map_map.
replace (a + 16 * Z.of_nat 0) with a by lia. f_equal. apply map_ext. intros k. f_equal. f_equal. lia.
Qed.

Lemma iovs_total_ok : forall mp iovs bufs,
Forall2 (iov_ok mp) iovs bufs -> iovs_total iovs = Z.of_nat (length (concat bufs)).
Proof.
intros mp iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
cbn [iovs_total fst snd concat] in *. subst l. rewrite length_app, IH.
rewrite unsigned_lit by lia. lia.
Qed.

Lemma cap_iovecs_id : forall mp iovs bufs left,
Forall2 (iov_ok mp) iovs bufs -> Z.of_nat (length (concat bufs)) <= left ->
cap_iovecs_aux iovs left = iovs.
Proof.
intros mp iovs bufs left H. revert left. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; intros left Hleft; [reflexivity|].
cbn [cap_iovecs_aux fst snd concat] in *. subst l. rewrite length_app in Hleft.
rewrite unsigned_lit by lia. rewrite Z.min_r by lia. rewrite IH by lia. reflexivity.
Qed.

Lemma gather_prefix_ok : forall mp iovs bufs,
Forall2 (iov_ok mp) iovs bufs -> gather_prefix mp iovs = concat bufs.
Proof.
intros mp iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
cbn [gather_prefix fst snd concat] in *. subst l.
rewrite <- (wa_unsigned_id b). rewrite (readable_bytes_bytes_in bs) by (first [exact Hb | lia]).
rewrite unsigned_lit, Z.eqb_refl by lia. rewrite IH. reflexivity.
Qed.

Lemma read_bytes_aux_wr_at : forall segs m a n k,
wr_at segs m a n -> Z.of_nat k <= n ->
read_bytes_aux (wview segs m) (wa a) k <> None.
Proof.
intros segs m a n k W Hk. destruct W as (Ha & Hn & H). revert a n Ha Hn H Hk.
induction k as [|k IH]; intros a n Ha Hn H Hk; cbn [read_bytes_aux]; [discriminate|].
destruct (wview segs m (wa a)) eqn:E.
2:{ exfalso. apply (H 0); [lia|]. rewrite Z.add_0_r. exact E. }
rewrite wa_succ.
assert (IH' : read_bytes_aux (wview segs m) (wa (a + 1)) k <> None).
{ apply (IH (a + 1) (n - 1)); try lia. intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
destruct (read_bytes_aux (wview segs m) (wa (a + 1)) k); [discriminate|]. exfalso; apply IH'; reflexivity.
Qed.

Inductive node : Type :=
| NWritev (fd : Z) (bufs : list (list byte))
| NOpen (path : list byte)
| NRead (fd : Z) (buf : Z) (count : Z)
| NClose (fd : Z)
| NIoctl (fd : Z) (req : Z)
| NSetTid
| NExit (code : Z)
| NBrk (req : Z)
| NMmap (addr len prot flags : Z)
| NMunmap (addr len : Z)
| NMprotect (addr len prot : Z).

Definition pure_input (no : Z) (args : list word) : SyscallInput :=
mkInput (Z_to_bv 64 no) args (fun _ => None) (fun _ => None).

Definition node_input (n : node) : option SyscallInput :=
match n with
| NBrk req => Some (pure_input 214 [Z_to_bv 64 req])
| NMmap addr len prot flags =>
Some (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
| NMunmap addr len => Some (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len])
| NMprotect addr len prot => Some (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot])
| _ => None
end.

Definition access_ok_walk_max : Z := 16777216.
Definition task_size_max : Z := TASK_SIZE.

Definition writev_bytes_max : Z := 67108864.

Section AtNode.
Variable segs : list Segment.

Definition at_node (n : node) (ms : machine_state) : Prop :=
match n with
| NWritev fd bufs =>
ms_svc_pending ms = Some (Z_to_bv 64 66) /\
(fd = 1 \/ fd = 2) /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
(1 <= length bufs <= 1024)%nat /\
Z.of_nat (length (concat bufs)) <= writev_bytes_max /\
ms_rom ms = seg_rom segs /\
exists iovs : list (word * word),
bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs /\

bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE /\
Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= TASK_SIZE) iovs
| NOpen path =>
ms_svc_pending ms = Some (Z_to_bv 64 56) /\
areg ms 10 = Z_to_bv 64 (-100) /\
Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = 0 /\
~ In (Z_to_bv 8 0) path /\

path_has_slash path = false /\ path_eqb path dotdot_path = false /\
ms_rom ms = seg_rom segs /\
bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
| NRead fd buf count =>
ms_svc_pending ms = Some (Z_to_bv 64 63) /\
3 <= fd < 2^32 /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 11 = Z_to_bv 64 buf /\
areg ms 12 = Z_to_bv 64 count /\
1 <= count <= access_ok_walk_max /\
buf + count <= task_size_max /\
wr_at segs (ms_mem ms) buf count
| NClose fd =>
ms_svc_pending ms = Some (Z_to_bv 64 57) /\
3 <= fd < 2^32 /\
areg ms 10 = Z_to_bv 64 fd
| NIoctl fd req =>
ms_svc_pending ms = Some (Z_to_bv 64 29) /\
0 <= fd <= 2 /\ req = 21523 /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 11 = Z_to_bv 64 req
| NSetTid =>
ms_svc_pending ms = Some (Z_to_bv 64 96)
| NExit code =>
(ms_svc_pending ms = Some (Z_to_bv 64 93) \/ ms_svc_pending ms = Some (Z_to_bv 64 94)) /\
areg ms 10 = Z_to_bv 64 code
| NBrk req =>
ms_svc_pending ms = Some (Z_to_bv 64 214) /\
areg ms 10 = Z_to_bv 64 req
| NMmap addr len prot flags =>
ms_svc_pending ms = Some (Z_to_bv 64 222) /\
areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
areg ms 12 = Z_to_bv 64 prot /\ areg ms 13 = Z_to_bv 64 flags /\
areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0
| NMunmap addr len =>
ms_svc_pending ms = Some (Z_to_bv 64 215) /\
areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
| NMprotect addr len prot =>
ms_svc_pending ms = Some (Z_to_bv 64 226) /\
areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 prot
end.

End AtNode.

Ltac at_node_red :=
cbn [at_node]; unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
repeat match goal with
| |- context [reg_get ?R ?r] =>
let p := eval vm_compute in (bv_key r) in
let R' := eval hnf in R in
change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
cbv beta iota delta [tget]
end.

Ltac split_spine :=
lazymatch goal with
| |- _ /\ _ => split; [|split_spine]
| |- _ => idtac
end.

Definition canon (e : resp) : resp :=
mkEffectU (eff_ret e) (eff_writes e) (eff_zeros e) (eff_unmaps e) (eff_copies e) [].

Lemma canon_with_copyins : forall rs e, canon (with_copyins rs e) = canon e.
Proof. intros rs [r ws zs us cs ci]. reflexivity. Qed.

Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).

Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
(exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
\/ (let fd := alloc_fd (m_fds mo) in
fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).

Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
match n with
| NWritev fd bufs =>
mo' = mo /\
let all := concat bufs in
(all = [] /\ eff = eff0 (Z_to_bv 64 0) /\ evs = [])
\/ (exists k : Z, 1 <= k <= Z.of_nat (length all) /\ eff = eff0 (Z_to_bv 64 k) /\
evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) all))
| NOpen path =>
evs = [] /\
if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
else match path with
| [] => eff = efferr ENOENT /\ mo' = mo
| _ => if path_eqb path dot_path then open_result mo FdDir eff mo'
else match fs_lookup (m_fs mo) path with
| None => eff = efferr ENOENT /\ mo' = mo
| Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) eff mo'
end
end
| NRead fd buf count =>
evs = [] /\
match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
| None => eff = efferr EBADF /\ mo' = mo
| Some FdDir => eff = efferr EISDIR /\ mo' = mo
| Some (FdFile p off) =>
match fs_lookup (m_fs mo) p with
| None => False
| Some data =>
let bs := file_read data off (Z_to_bv 64 count) in
eff = mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [] /\
mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
end
| Some (FdChannel _) | Some (FdFileW _ _) | Some (FdFileA _ _) | Some (FdFileRW _ _)
| Some (FdSocket _) | Some (FdPipe _ _) | Some (FdDevNull _ _) | Some FdUrandom => False
end
| NClose fd =>
evs = [] /\ 3 <= fd < 2^32 /\
match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
| None => eff = efferr EBADF /\ mo' = mo
| Some _ => eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
end
| NIoctl fd req => evs = [] /\ eff = efferr ENOTTY /\ mo' = mo
| NSetTid =>
evs = [] /\ exists t, eff = eff0 t /\
match m_tid mo with
| Some t0 => t = t0 /\ mo' = mo
| None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
end
| NExit _ => False
| NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ =>
evs = [] /\
match node_input n with
| Some i => syscall_spec i mo (Ok eff mo' evs)
| None => False
end
end.

Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
match n with
| NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
| _ => False
end.

Definition minv (mo : Model) : Prop :=
fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
(forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
(forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
(forall k e, fd_lookup (m_fds mo) k = Some e ->
match e with FdChannel _ | FdFile _ _ | FdDir => True | _ => False end) /\
(forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
m_vm_lazy mo = [] /\ m_vm_materialized mo = [] /\

sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi.

Definition munmap_safe_b (addr len : word) (h : VmMaps) : bool :=
if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then true
else
let nZ := page_round_up_Z (bv_unsigned len) in
if (TASK_SIZE <? bv_unsigned addr + nZ) then true
else
let n := Z_to_bv 64 nZ in
map_has (vm_maps h) addr n || munmap_free_ok h addr nZ.

Definition mprotect_safe_b (addr len prot : word) (h : VmMaps) : bool :=
if mprotect_grows_conflict_b prot then true
else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
else if w_is0 len then true
else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len)) then true
else if mprotect_modeled_b prot then
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
(map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n)
|| (map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n)
else false.

Definition mmap_fixed_safe_b (addr len : word) (h : VmMaps) : bool :=
let nZ := page_round_up_Z (bv_unsigned len) in
if (two_pow_64 <=? bv_unsigned addr + nZ) then true
else if negb (bv_unsigned addr + nZ <=? alloc_top h) then false
else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
else if negb (0 <? bv_unsigned addr) then false
else
let n := Z_to_bv 64 nZ in
(region_free (vm_reserved h) addr n && map_contains (vm_maps h) addr n)
|| region_free (vm_reserved h ++ vm_maps h) addr n.

Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
negb (mmap_noreserve_b flags) && mmap_off_aligned_b off && mmap_anon_b flags &&
(if w_is0 len then mmap_plain_anon_b flags
else mmap_modeled_b prot flags off
|| mmap_noaccess_b prot flags off
|| ((mmap_fixed_noaccess_b prot flags off || mmap_fixed_rw_b prot flags off)
&& mmap_fixed_safe_b addr len h)).

Definition nsafe (n : node) (mo : Model) : Prop :=
match n with
| NMmap addr len prot flags =>
mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) (m_vmmaps mo) = true
| NMunmap addr len => munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true
| NMprotect addr len prot =>
mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (m_vmmaps mo) = true
| _ => True
end.

Section Generic.
Variable segs : list Segment.

Lemma sstep_svc_inv : forall ms mo x8 evs X,
ms_svc_pending ms = Some x8 -> sstep segs (mkCfg ms mo) evs X ->
(exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\ m_halted mo' = None /\
materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
X = SNext (mkCfg (nret ms eff) mo''))
\/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = None /\
materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\ evs = [] /\ X = SError)
\/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
\/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError)

\/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo')).
Proof.
intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
- left. eexists _, _, _. eauto.
- right; left. eexists _, _, _. eauto 6.
- right; right; left. eexists _, _, _, _. eauto.
- right; right; right; right. eexists _, _, _, _. eauto.
- right; right; right; left. auto.
Qed.

Definition node_facts_at (i : SyscallInput) (mo : Model) (P : resp -> Model -> list event -> Prop) : Prop :=
(forall eff mo' evs, check_syscall i eff mo = CheckOk mo' evs -> P (canon eff) mo' evs) /\
(forall rsp mo' evs, P rsp mo' evs -> exists eff, canon eff = rsp /\ check_syscall i eff mo = CheckOk mo' evs) /\
(forall eff, check_syscall i eff mo <> CheckUnmodeled) /\
(forall rsp mo' evs, P rsp mo' evs -> m_halted mo' = None /\ minv mo').

Lemma exit_kit : forall ms mo x8 code,
ms_svc_pending ms = Some x8 -> m_halted mo = None ->
(forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs <->
eff = eff0 (Z_to_bv 64 0) /\ mo' = with_halted code mo /\ evs = []) ->
(forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) ->
(forall evs X, sstep segs (mkCfg ms mo) evs X ->
X = SNext (mkCfg ms (with_halted code mo)) /\ evs = [ExitEv code (m_fs mo)])
/\ sstep segs (mkCfg ms mo) [ExitEv code (m_fs mo)] (SNext (mkCfg ms (with_halted code mo))).
Proof.
intros ms mo x8 code Hsvc Hh Hchar Hnu. split.
- intros evs X Hst. destruct (sstep_svc_inv _ _ _ _ _ Hsvc Hst)
as [(eff & mo' & mo'' & Hs & Hh' & Hmat & ->) | [(eff & mo' & evs0 & Hs & Hh' & Hmat & -> & ->)
| [(eff & mo' & evs0 & code' & Hs & Hh' & -> & ->) | [(Hs & -> & ->)
| (eff & mo' & evs0 & sig & Hs & Hk & -> & ->)]]]].
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _).
rewrite m_halted_with_halted in Hh'. discriminate.
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _).
rewrite m_halted_with_halted in Hh'. discriminate.
+ apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & ->).
rewrite m_halted_with_halted in Hh'. inversion Hh'; subst.
rewrite m_fs_with_halted. split; reflexivity.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
+ exfalso. apply check_syscall_ok_iff in Hs. apply Hchar in Hs as (_ & -> & _).
unfold m_killed, with_halted in Hk. cbn [m_proc procst_killed] in Hk. discriminate.
- replace [ExitEv code (m_fs mo)] with ([] ++ [ExitEv code (m_fs (with_halted code mo))])
by (rewrite m_fs_with_halted; reflexivity).
eapply sstep_exit; [exact Hh|exact Hsvc| |apply m_halted_with_halted|].
+ apply check_syscall_ok_iff. apply Hchar. repeat split; reflexivity.
+ unfold m_killed, with_halted. cbn [m_proc procst_killed]. reflexivity.
Qed.

End Generic.

Lemma m_vm_lazy_with_fds : forall v m, m_vm_lazy (with_fds v m) = m_vm_lazy m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_materialized_with_fds : forall v m, m_vm_materialized (with_fds v m) = m_vm_materialized m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_lazy_with_tid : forall v m, m_vm_lazy (with_tid v m) = m_vm_lazy m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_materialized_with_tid : forall v m, m_vm_materialized (with_tid v m) = m_vm_materialized m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_lazy_with_halted : forall v m, m_vm_lazy (with_halted v m) = m_vm_lazy m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_materialized_with_halted : forall v m, m_vm_materialized (with_halted v m) = m_vm_materialized m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps : forall v m, m_vm_lazy (with_vmmaps v m) = m_vm_lazy m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps : forall v m, m_vm_materialized (with_vmmaps v m) = m_vm_materialized m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_lazy_with_stdin : forall v m, m_vm_lazy (with_stdin v m) = m_vm_lazy m.
Proof. intros v []; reflexivity. Qed.
Lemma m_vm_materialized_with_stdin : forall v m, m_vm_materialized (with_stdin v m) = m_vm_materialized m.
Proof. intros v []; reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_fds m_vm_materialized_with_fds m_vm_lazy_with_tid m_vm_materialized_with_tid
m_vm_lazy_with_halted m_vm_materialized_with_halted m_vm_lazy_with_vmmaps m_vm_materialized_with_vmmaps
m_vm_lazy_with_stdin m_vm_materialized_with_stdin : model.

Lemma ca_no_arm_eventfd2' : ca_no arm_eventfd2 = 19. Proof. reflexivity. Qed.
Lemma ca_no_arm_epoll_create1' : ca_no arm_epoll_create1 = 20. Proof. reflexivity. Qed.
Lemma ca_no_arm_epoll_ctl' : ca_no arm_epoll_ctl = 21. Proof. reflexivity. Qed.
Lemma ca_no_arm_epoll_pwait' : ca_no arm_epoll_pwait = 22. Proof. reflexivity. Qed.
Lemma ca_no_arm_pread64' : ca_no arm_pread64 = 67. Proof. reflexivity. Qed.
Lemma ca_no_arm_pwrite64' : ca_no arm_pwrite64 = 68. Proof. reflexivity. Qed.
Lemma ca_no_arm_tkill' : ca_no arm_tkill = 130. Proof. reflexivity. Qed.
Lemma ca_no_arm_tgkill' : ca_no arm_tgkill = 131. Proof. reflexivity. Qed.
Lemma ca_no_arm_uname' : ca_no arm_uname = 160. Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_eventfd2' ca_no_arm_epoll_create1' ca_no_arm_epoll_ctl' ca_no_arm_epoll_pwait'
ca_no_arm_pread64' ca_no_arm_pwrite64' ca_no_arm_tkill' ca_no_arm_tgkill' ca_no_arm_uname' : arm_unfold.

Section PerNode.
Variable segs : list Segment.

Definition node_facts (ms : machine_state) (mo : Model) (n : node) : Prop :=
exists x8, ms_svc_pending ms = Some x8 /\ node_facts_at (sys_input segs ms x8) mo (nstep n mo).

Lemma lookup_ca_29 : lookup_ca checked_table 29 = Some arm_ioctl. Proof. reflexivity. Qed.
Lemma lookup_ca_56 : lookup_ca checked_table 56 = Some arm_openat. Proof. reflexivity. Qed.
Lemma lookup_ca_57 : lookup_ca checked_table 57 = Some arm_close. Proof. reflexivity. Qed.
Lemma lookup_ca_63 : lookup_ca checked_table 63 = Some arm_read. Proof. reflexivity. Qed.
Lemma lookup_ca_66 : lookup_ca checked_table 66 = Some arm_writev. Proof. reflexivity. Qed.
Lemma lookup_ca_93 : lookup_ca checked_table 93 = Some arm_exit. Proof. reflexivity. Qed.
Lemma lookup_ca_94 : lookup_ca checked_table 94 = Some arm_exit_group. Proof. reflexivity. Qed.
Lemma lookup_ca_96 : lookup_ca checked_table 96 = Some arm_set_tid_address. Proof. reflexivity. Qed.
Lemma lookup_ca_214 : lookup_ca checked_table 214 = Some arm_brk. Proof. reflexivity. Qed.
Lemma lookup_ca_215 : lookup_ca checked_table 215 = Some arm_munmap. Proof. reflexivity. Qed.
Lemma lookup_ca_222 : lookup_ca checked_table 222 = Some arm_mmap. Proof. reflexivity. Qed.
Lemma lookup_ca_226 : lookup_ca checked_table 226 = Some arm_mprotect. Proof. reflexivity. Qed.

Lemma check_syscall_arm : forall i eff m c,
lookup_ca checked_table (bv_unsigned (in_sysno i)) = Some c -> check_syscall i eff m = ca_check c i eff m.
Proof. intros i eff m c H. unfold check_syscall. rewrite H. reflexivity. Qed.

Ltac lookup_solve :=
first [ exact lookup_ca_29 | exact lookup_ca_56 | exact lookup_ca_57 | exact lookup_ca_63 | exact lookup_ca_66
| exact lookup_ca_93 | exact lookup_ca_94 | exact lookup_ca_96 | exact lookup_ca_214 | exact lookup_ca_215
| exact lookup_ca_222 | exact lookup_ca_226 ].

Ltac arm_unfold_K K :=
lazymatch K with
| 29 => rewrite ca_check_arm_ioctl | 56 => rewrite ca_check_arm_openat | 57 => rewrite ca_check_arm_close
| 63 => rewrite ca_check_arm_read | 66 => rewrite ca_check_arm_writev | 93 => rewrite ca_check_arm_exit
| 94 => rewrite ca_check_arm_exit_group | 96 => rewrite ca_check_arm_set_tid_address | 214 => rewrite ca_check_arm_brk
| 215 => rewrite ca_check_arm_munmap | 222 => rewrite ca_check_arm_mmap | 226 => rewrite ca_check_arm_mprotect
| _ => autorewrite with arm_unfold
end.
Ltac dispatch K :=
erewrite check_syscall_arm;
[| rewrite in_sysno_si; change (bv_unsigned (Z_to_bv 64 K)) with K; lookup_solve];
arm_unfold_K K;
rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

Lemma abi_low32_small : forall z, 0 <= z < 2^32 -> abi_low32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma fd_lookup_filter : forall fds fd k, bv_eqb fd k = false ->
fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) k = fd_lookup fds k.
Proof.
induction fds as [|[k' e] fds IH]; intros fd k Hne; [reflexivity|].
cbn [List.filter fst]. destruct (bv_eqb k' fd) eqn:E; cbn [negb fd_lookup].
- apply bv_eqb_eq in E; subst k'. rewrite Hne. apply IH. exact Hne.
- rewrite IH by exact Hne. reflexivity.
Qed.

Lemma fd_lookup_insert : forall fds fd e k,
fd_lookup (fd_insert fds fd e) k = if bv_eqb fd k then Some e else fd_lookup fds k.
Proof.
intros. unfold fd_insert. cbn [fd_lookup]. destruct (bv_eqb fd k) eqn:E; [reflexivity|].
apply fd_lookup_filter. exact E.
Qed.

Lemma fd_lookup_remove : forall fds fd k,
fd_lookup (fd_remove fds fd) k = if bv_eqb fd k then None else fd_lookup fds k.
Proof.
intros. unfold fd_remove. destruct (bv_eqb fd k) eqn:E.
- apply bv_eqb_eq in E; subst k. induction fds as [|[k' e] fds IH]; [reflexivity|].
cbn [List.filter fst]. destruct (bv_eqb k' fd) eqn:E'; cbn [negb fd_lookup]; [exact IH|].
rewrite E'. exact IH.
- apply fd_lookup_filter. exact E.
Qed.

Lemma exit_check : forall ms mo c x8 eff,
at_node segs (NExit c) ms -> ms_svc_pending ms = Some x8 ->
check_syscall (sys_input segs ms x8) eff mo
= check_ret_only eff (Z_to_bv 64 0) (with_halted (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) mo) [].
Proof.
intros ms mo c x8 eff [Hsvc Ha0] Hx8.
destruct Hsvc as [Hsvc|Hsvc]; rewrite Hsvc in Hx8; inversion Hx8; subst;
[dispatch 93 | dispatch 94]; unfold check_exit; rewrite Ha0; reflexivity.
Qed.

Lemma clear_copyins_canon : forall e, clear_copyins e = canon e.
Proof. intros [r ws zs us cs ci]. reflexivity. Qed.

Lemma canon_of_canonical : forall e, eff_copyins e = [] -> canon e = e.
Proof. intros [r ws zs us cs ci] H. cbn in H. subst. reflexivity. Qed.

Lemma eff_copyins_with_copyins : forall rs e, eff_copyins (with_copyins rs e) = rs.
Proof. intros rs [r ws zs us cs ci]. reflexivity. Qed.

Lemma clear_with_copyins : forall rs e, clear_copyins (with_copyins rs e) = canon e.
Proof. intros rs [r ws zs us cs ci]. reflexivity. Qed.

Definition open_check (path : list byte) (eff : resp) (mo : Model) : check_result :=
if (path_max <=? length path)%nat then check_ret_only eff (errno_ret ENAMETOOLONG) mo []
else match path with
| [] => check_ret_only eff (errno_ret ENOENT) mo []
| _ => if path_eqb path dot_path
then check_open_result eff mo (fun fd => with_fds (fd_insert (m_fds mo) fd FdDir) mo)
else match fs_lookup (m_fs mo) path with
| None => check_ret_only eff (errno_ret ENOENT) mo []
| Some _ => check_open_result eff mo
(fun fd => with_fds (fd_insert (m_fds mo) fd (FdFile path (Z_to_bv 64 0))) mo)
end
end.

Lemma check_open_result_ok_iff : forall eff mo ent mo' evs,
check_open_result eff mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) = CheckOk mo' evs <->
(open_result mo ent eff mo' /\ evs = []).
Proof.
intros [ret ws zs us cs ci] mo ent mo' evs. unfold check_open_result, check_new_fd_result, open_result, efferr, eff0. split.
- intro H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in openat_errnos ret) eqn:Herr.
+ inversion H; subst. apply errno_ret_in_true in Herr as (e & HIn & ->). split; [|reflexivity]. left. exists e. auto.
+ destruct (fd_lookup (m_fds mo) ret) eqn:Hlk; [discriminate|].
destruct (bv_eqb ret (alloc_fd (m_fds mo))) eqn:Heq; [|discriminate].
inversion H; subst. apply bv_eqb_eq in Heq. subst ret. split; [|reflexivity]. right. auto.
- intros [[(e & HIn & Heff & ->) | (Hlk & Heff & ->)] ->]; inversion Heff; subst.
+ rewrite (errno_ret_in_intro _ e HIn). reflexivity.
+ rewrite errno_ret_in_alloc_fd by reflexivity. rewrite Hlk, bv_eqb_refl. reflexivity.
Qed.

Lemma open_result_canonical : forall mo ent eff mo', open_result mo ent eff mo' -> eff_copyins eff = [].
Proof. intros mo ent eff mo' [(e & _ & -> & _) | (_ & -> & _)]; reflexivity. Qed.

Lemma open_check_spec : forall ms mo path eff,
at_node segs (NOpen path) ms ->
check_syscall (sys_input segs ms (Z_to_bv 64 56)) eff mo =
check_copyins_after [(areg ms 11, cstr_access_len_aux (ms_read_byte ms) (areg ms 11) path_max)] eff
(open_check path (clear_copyins eff) mo).
Proof.
intros ms mo path eff (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hdd & Hrom & Hp).
pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
dispatch 56. unfold check_openat. rewrite Ha0, in_mem_si.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv zeta. f_equal.
unfold Open.check_openat_body, open_check.
rewrite <- (wa_unsigned_id (areg ms 11)) at 1. unfold read_cstr.
destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
- rewrite (read_cstr_aux_toolong_bytes_in path_max path); [reflexivity|exact Hlong|exact Hnz|].
apply bytes_in_app in Hin as [Hin _]. exact Hin.
- rewrite (read_cstr_aux_bytes_in path path_max); [|lia|exact Hnz|exact Hin].
cbv iota beta.
unfold Open.check_openat_resolved, Open.check_openat_read, path_is_dirref.
rewrite Hsl, Hdd, Bool.orb_false_r. cbv iota beta.
destruct path as [|c path']; [reflexivity|].
change (path_eqb (c :: path') []) with false.
change (bv_eqb (fd32 (Z_to_bv 64 (-100))) AT_FDCWD32) with true. cbv iota beta.
rewrite Hfl. change (Z.eqb 0 0) with true. cbv iota beta. reflexivity.
Qed.

Lemma open_check_ok_iff : forall path eff mo mo' evs,
open_check path eff mo = CheckOk mo' evs <-> nstep (NOpen path) mo eff mo' evs.
Proof.
intros path eff mo mo' evs. unfold open_check. cbn [nstep].
destruct (path_max <=? length path)%nat.
{ rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
destruct path as [|c path']. { rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
destruct (path_eqb (c :: path') dot_path). { rewrite check_open_result_ok_iff. tauto. }
destruct (fs_lookup (m_fs mo) (c :: path')).
- rewrite check_open_result_ok_iff. tauto.
- rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto.
Qed.

Lemma open_nstep_canonical : forall path eff mo mo' evs, nstep (NOpen path) mo eff mo' evs -> eff_copyins eff = [].
Proof.
intros path eff mo mo' evs [_ H].
destruct (path_max <=? length path)%nat. { destruct H as [-> _]. reflexivity. }
destruct path as [|c path']. { destruct H as [-> _]. reflexivity. }
destruct (path_eqb (c :: path') dot_path). { eapply open_result_canonical; exact H. }
destruct (fs_lookup (m_fs mo) (c :: path')). { eapply open_result_canonical; exact H. }
destruct H as [-> _]. reflexivity.
Qed.

Lemma open_check_no_unmodeled : forall path eff mo, open_check path eff mo <> CheckUnmodeled.
Proof.
intros path eff mo. unfold open_check.
destruct (path_max <=? length path)%nat; [apply check_ret_only_no_unmodeled|].
destruct path; [apply check_ret_only_no_unmodeled|].
destruct (path_eqb _ dot_path); [apply check_new_fd_result_no_unmodeled|].
destruct (fs_lookup (m_fs mo) _); [apply check_new_fd_result_no_unmodeled|apply check_ret_only_no_unmodeled].
Qed.

Definition read_check (fd buf count : Z) (eff : resp) (mo : Model) : check_result :=
match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
| None => check_ret_only eff (errno_ret EBADF) mo []
| Some FdDir => check_ret_only eff (errno_ret EISDIR) mo []
| Some (FdFile p off) =>
match fs_lookup (m_fs mo) p with
| None => CheckReject
| Some data =>
let bs := file_read data off (Z_to_bv 64 count) in
let m' := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo in
match bs, eff with
| [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
| _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
if bv_eqb a (Z_to_bv 64 buf) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
then CheckOk m' [] else CheckReject
| _, _ => CheckReject
end
end
| _ => CheckReject
end.

Lemma length_file_read_le : forall data off c, (length (file_read data off c) <= word_to_nat c)%nat.
Proof. intros. rewrite file_read_unguarded. apply firstn_le_length. Qed.

Lemma read_bytes_map_wr_at : forall ms buf count n,
wr_at segs (ms_mem ms) buf count -> 0 <= n <= count -> count < 2^64 ->
read_bytes_map (ms_writable_byte segs ms) (Z_to_bv 64 buf) (Z_to_bv 64 n) <> None.
Proof.
intros ms buf count n Hwr Hn Hc64. pose proof Hwr as (Hb & Hc & _).
rewrite read_bytes_map_eq. unfold ms_writable_byte, word_to_nat. rewrite unsigned_lit by lia.
change (Z_to_bv 64 buf) with (wa buf).
exact (read_bytes_aux_wr_at segs (ms_mem ms) buf count (Z.to_nat n) Hwr ltac:(lia)).
Qed.

Lemma access_okb_wr_at : forall ms buf count,
wr_at segs (ms_mem ms) buf count -> 1 <= count <= access_ok_walk_max -> buf + count <= task_size_max ->
access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true.
Proof.
intros ms buf count Hwr Hc Htop. pose proof Hwr as (Hb & Hc2 & _). unfold access_ok_walk_max, task_size_max, TASK_SIZE in *.
unfold access_okb, TASK_SIZE. rewrite !unsigned_lit by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
Qed.

Lemma listN_eqb_refl : forall l, listN_eqb l l = true.
Proof. intros. apply listN_eqb_eq. reflexivity. Qed.

Lemma read_check_no_unmodeled : forall fd buf count eff mo, read_check fd buf count eff mo <> CheckUnmodeled.
Proof.
intros fd buf count eff mo. unfold read_check.
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|dnr dnw| ]|]; try discriminate; try apply check_ret_only_no_unmodeled.
destruct (fs_lookup (m_fs mo) p); [|discriminate]. cbv zeta.
destruct (file_read _ _ _); [apply check_ret_only_no_unmodeled|].
destruct eff as [ret [|[a bs'] [|? ?]] [|? ?] [|? ?] [|? ?] [|? ?]]; try discriminate.
destruct (_ && _); discriminate.
Qed.

Definition writev_check (fd : Z) (all : list byte) (reads : list (word * nat)) (pref : nat -> list (word * nat))
(eff : resp) (mo : Model) : check_result :=
if Nat.eqb (length all) 0 then check_ret_only_copyins reads eff (Z_to_bv 64 0) mo []
else match eff with
| mkEffectU ret [] [] [] [] ci =>
if (1 <=? bv_unsigned ret) && (bv_unsigned ret <=? Z.of_nat (length all)) && negb (addr_is_error_b ret)
then if access_ranges_eqb ci (reads ++ pref (Z.to_nat (bv_unsigned ret)))
then CheckOk mo (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) all))
else CheckReject
else CheckReject
| _ => CheckReject
end.

Lemma iovs_ok_of_at : forall ms iovs bufs,
ms_rom ms = seg_rom segs ->
Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
Z.of_nat (length (concat bufs)) < 2^63 ->
Forall2 (iov_ok (ms_read_byte ms)) iovs bufs.
Proof.
intros ms iovs bufs Hrom H. induction H as [|iov bs iovs bufs [Hl Hb] _ IH]; intros Hlen; [constructor|].
cbn [concat] in Hlen. rewrite length_app in Hlen.
constructor.
- split; [exact Hl|]. split; [lia|]. eapply bytes_at_in; eassumption.
- apply IH. lia.
Qed.

Lemma access_okb_le : forall (b : word) len, 0 <= len -> bv_unsigned b + len <= TASK_SIZE -> access_okb b len = true.
Proof.
intros b len H0 H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b).
apply andb_true_intro; split; apply Z.leb_le; unfold TASK_SIZE in *; lia.
Qed.

Lemma import_iovecs_bytes_in : forall iovs bufs mp a,
bytes_in mp a (iovec_bytes iovs) -> Forall2 (iov_ok mp) iovs bufs ->
(1 <= length iovs <= 1024)%nat ->
a + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->
Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= TASK_SIZE) iovs ->
import_iovecs mp (wa a) (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs /\
import_iovecs_accesses mp (wa a) (Z_to_bv 64 (Z.of_nat (length iovs))) = copy_iovecs_accesses mp (wa a) (length iovs).
Proof.
intros iovs bufs mp a Hin Hok Hlen Ha Hb.
pose proof Hin as (Ha0 & _ & _).
pose proof (copy_iovecs_aux_bytes_in iovs bufs mp a Hin Hok) as Hcp.
assert (Hau : bv_unsigned (wa a) = a) by (unfold wa; rewrite unsigned_lit by (unfold TASK_SIZE in *; lia); reflexivity).
unfold import_iovecs, import_iovecs_accesses.
destruct iovs as [|[b l] [|iov2 rest]]; [cbn in Hlen; lia| |].
-
inversion Hok as [|? bs ? bufs' Hiov Hnil]; subst. inversion Hnil; subst.
destruct Hiov as (Hl & Hl63 & Hbin). cbn [fst snd] in Hl, Hbin.
change (Z.of_nat (length [(b, l)])) with 1. rewrite bv_eqb_refl.
rewrite (access_okb_le (wa a) 16) by (cbn [length Z.of_nat] in Ha; lia). cbn [negb].
cbn [iovec_bytes flat_map fst snd] in Hin. rewrite app_nil_r in Hin.
apply bytes_in_app in Hin as [H1 H2]. rewrite length_le8 in H2.
unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
rewrite wa_add. change (bv_unsigned (8%bv : word)) with 8. replace (a + Z.of_nat 8) with (a + 8) in H2 by lia.
rewrite (read_u64_bytes_in _ _ _ H2). subst l. rewrite unsigned_lit by lia.
replace (2 ^ 63 <=? Z.of_nat (length bs)) with false by (symmetry; apply Z.leb_gt; lia).
inversion Hb as [|? ? Hb1 _]; subst. cbn [fst snd] in Hb1. rewrite unsigned_lit in Hb1 by lia.
rewrite unsigned_lit by lia.
rewrite (access_okb_le b) by (unfold MAX_RW_COUNT; lia). cbn [negb]. split; [reflexivity|].
cbn [copy_iovecs_accesses length]. unfold read_iovec_entry. rewrite (read_u64_bytes_in _ _ _ H1).
rewrite wa_add. change (bv_unsigned (8%bv : word)) with 8. rewrite (read_u64_bytes_in _ _ _ H2).
rewrite unsigned_lit by lia. replace (2 ^ 63 <=? Z.of_nat (length bs)) with false by (symmetry; apply Z.leb_gt; lia).
reflexivity.
-
set (iovs := (b, l) :: iov2 :: rest) in *.
assert (Hn1 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 1) = false).
{ unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. cbn [iovs length] in *. lia. }
assert (Hn0 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 0) = false).
{ unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. cbn [iovs length] in *. lia. }
rewrite Hn1, Hn0. rewrite unsigned_lit by lia.
replace (IOV_MAX <? Z.of_nat (length iovs)) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
rewrite (access_okb_le (wa a)) by lia. cbn [negb].
rewrite word_to_nat_of_nat by lia. rewrite Hcp.
replace (iovs_access_okb iovs) with true.
2:{ symmetry. unfold iovs_access_okb. apply forallb_forall. intros [b' l'] Hin'.
rewrite Forall_forall in Hb. specialize (Hb _ Hin'). cbn [fst snd] in *.
apply access_okb_le; [apply bv_unsigned_in_range| exact Hb]. }
split; reflexivity.
Qed.

Definition vm_only (m m' : Model) : Prop :=
m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
m_tid m' = m_tid m /\ m_stdin m' = m_stdin m.

Definition lazy_kept (m m' : Model) : Prop :=
(m_vm_lazy m = [] -> m_vm_lazy m' = []) /\ (m_vm_lazy m = [] -> m_vm_materialized m = [] -> m_vm_materialized m' = []).

Definition sp_kept (m m' : Model) : Prop := vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).

Lemma sp_vmmaps_with_vm_backing : forall lz mt m, m_vmmaps (with_vm_backing lz mt m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma sp_vmmaps_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma sp_vmmaps_forget_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. induction rs as [|[a n] rs IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. Qed.
Lemma sp_vmmaps_backing : forall flags a n m, m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing, vm_add_lazy. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma sp_vmmaps_replacement : forall flags a n m, m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_replacement. rewrite sp_vmmaps_backing. reflexivity. Qed.
Lemma sp_vmmaps_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. reflexivity. Qed.
Lemma sp_vmmaps_brk_next : forall m req r, m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof. intros. unfold with_brk_next. rewrite sp_vmmaps_forget_ranges. reflexivity. Qed.

End PerNode.

Definition exit_code (c : Z) : word := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).

Lemma exit_node_facts : forall segs ms mo c,
at_node segs (NExit c) ms -> m_halted mo = None ->
(forall evs X, sstep segs (mkCfg ms mo) evs X ->
X = SNext (mkCfg ms (with_halted (exit_code c) mo)) /\ evs = [ExitEv (exit_code c) (m_fs mo)])
/\ sstep segs (mkCfg ms mo) [ExitEv (exit_code c) (m_fs mo)] (SNext (mkCfg ms (with_halted (exit_code c) mo))).
Proof.
intros segs ms mo c Hat Hh.
assert (Hx : exists x8, ms_svc_pending ms = Some x8).
{ destruct (proj1 Hat) as [H|H]; eexists; exact H. }
destruct Hx as [x8 Hsvc].
apply (exit_kit segs ms mo x8 (exit_code c) Hsvc Hh).
- intros eff mo' evs. rewrite (exit_check segs ms mo c x8 eff Hat Hsvc). rewrite check_ret_only_ok_iff. unfold eff0, exit_code. tauto.
- intros eff. rewrite (exit_check segs ms mo c x8 eff Hat Hsvc). apply check_ret_only_no_unmodeled.
Qed.

