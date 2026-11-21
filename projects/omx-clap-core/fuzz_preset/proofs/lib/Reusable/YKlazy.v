(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YKlazy.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-10-30: lazy_in_maps_cf (ALedger_cf's alc_lazy_in_maps, YG0ncf.v) and its keep lemmas at the
   MODEL level: this file Requires only YK* / YM05 / YZ00 model files, so the start-up arms of YA02 / YA07 / YA08 /
   YA09 can call it (YGcfLazyMaps.v Requires YG0j / YG0b, which Require YA05 / YA08 / YA09: an import cycle there).
   Moved verbatim from YGcfLazyMaps.v: the definition, lim_cov_app / lim_cov_cons and the keeps for
   init, mmap, noaccess, add_lazy, backing, lim_mmap_range, noreserve, munmap; YGcfLazyMaps.v re-exports this file.
   Re-proved from YG0j.v:20-42 under the same statements: cov_app, cov_subtract_out, cov_lazy_interior_out.
   New: keeps for YK13.mprotect_model and YK02.brk_model, lim_noaccess_range (prot-0 twin of lim_mmap_range), and
   equation forms (_eq) of YA09's grant_post / slice_post / dest_post, stated over the records' own field
   equations so that no YA* name occurs here. No function is proved here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YK0v YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0g YK13 YK0x YK02.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The field's statement (YG0ncf.v alc_lazy_in_maps), named for the keep lemmas. *)
Definition lazy_in_maps_cf (md : Model) : Prop :=
forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true ->
YK0g.covered (vm_maps (m_vmmaps md)) x = true.

Lemma lim_cov_app : forall l1 l2 x, YK0g.covered (l1 ++ l2) x = (YK0g.covered l1 x || YK0g.covered l2 x)%bool.
Proof. intros l1 l2 x. unfold YK0g.covered. apply existsb_app. Qed.

Lemma lim_cov_cons : forall c l x, YK0g.covered (c :: l) x = (YK0g.in_iv c x || YK0g.covered l x)%bool.
Proof. reflexivity. Qed.

(* YG0j.v:20-42, re-proved here (YG0j Requires YA05 / YG0b); same statements, the same local names for YK0g's. *)
Section k.
Local Abbreviation covered := YK0g.covered.
Local Abbreviation ivs_wf := YK0g.ivs_wf.
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
destruct (lo' <? hi') eqn:E; [|reflexivity]. apply Z.ltb_lt in E. cbn [YK0g.covered existsb].
unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. cbn [fst snd].
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; lia). rewrite Bool.orb_false_r.
apply Bool.andb_false_iff. destruct (Z_lt_dec x lo'); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.
End k.

(* The init witness: the process's first model has no noaccess and no lazy range. *)
Lemma lazy_in_maps_init_cf : forall md, vm_noaccess (m_vmmaps md) = [] -> m_vm_lazy md = [] -> lazy_in_maps_cf md.
Proof. intros md E1 E2 x Hx. rewrite E1, E2 in Hx. cbn in Hx. discriminate Hx. Qed.

(* A plain map adds a mapping and touches neither list. *)
Lemma lazy_in_maps_mmap_cf : forall a n md, lazy_in_maps_cf md -> lazy_in_maps_cf (mmap_model a n md).
Proof.
intros a n md H x Hx.
change (YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true) in Hx.
change (YK0g.covered ((a, n) :: vm_maps (m_vmmaps md)) x = true).
rewrite lim_cov_cons, (H x Hx). apply orb_true_r.
Qed.

(* A PROT_NONE map adds the same range to both lists (YK13.v:192-197). *)
Lemma lazy_in_maps_noaccess_cf : forall a n md, lazy_in_maps_cf md -> lazy_in_maps_cf (YK13.noaccess_model a n md).
Proof.
intros a n md H x Hx.
change (YK0g.covered (((a, n) :: vm_noaccess (m_vmmaps md)) ++ m_vm_lazy md) x = true) in Hx.
change (YK0g.covered ((a, n) :: vm_maps (m_vmmaps md)) x = true).
cbn [app] in Hx. rewrite lim_cov_cons in Hx |- *.
apply orb_true_iff in Hx as [Hx|Hx]; [rewrite Hx; reflexivity|]. rewrite (H x Hx). apply orb_true_r.
Qed.

(* vm_add_lazy (State.v:4828-4829) adds the page interior of [a, a + n) (lazy_interior); it keeps the field when
   that range is mapped (it is, after the map that precedes it). *)
Lemma lazy_in_maps_add_lazy_cf : forall a n md, lazy_in_maps_cf md ->
bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
(forall x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n -> YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
lazy_in_maps_cf (vm_add_lazy a n md).
Proof.
intros a n md H Hb HR x Hx.
change (YK0g.covered (vm_noaccess (m_vmmaps md) ++ (lazy_interior a n ++ m_vm_lazy md)) x = true) in Hx.
change (YK0g.covered (vm_maps (m_vmmaps md)) x = true).
rewrite !lim_cov_app in Hx. apply orb_true_iff in Hx as [Hx|Hx].
- apply H. rewrite lim_cov_app, Hx. reflexivity.
- apply orb_true_iff in Hx as [Hx|Hx].
  + apply HR. destruct (Z_le_dec (bv_unsigned a) x); destruct (Z_lt_dec x (bv_unsigned a + bv_unsigned n)); try lia;
    rewrite (cov_lazy_interior_out a n x Hb ltac:(lia)) in Hx; discriminate Hx.
  + apply H. rewrite lim_cov_app, Hx. apply orb_true_r.
Qed.

(* The backing of a map (Mmap.v:704-705): vm_add_lazy when MAP_NORESERVE, else nothing. *)
Lemma lazy_in_maps_backing_cf : forall flags a n md, lazy_in_maps_cf md ->
bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
(forall x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n -> YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
lazy_in_maps_cf (with_mmap_backing flags a n md).
Proof.
intros flags a n md H Hb HR. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [|exact H].
exact (lazy_in_maps_add_lazy_cf a n md H Hb HR).
Qed.

(* The new map's own range is mapped right after mmap_model. *)
Lemma lim_mmap_range : forall a n md x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n ->
YK0g.covered (vm_maps (m_vmmaps (mmap_model a n md))) x = true.
Proof.
intros a n md x Hx. change (YK0g.covered ((a, n) :: vm_maps (m_vmmaps md)) x = true). rewrite lim_cov_cons.
unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. cbn [fst snd].
replace ((bv_unsigned a <=? x) && (x <? bv_unsigned a + bv_unsigned n))%bool with true; [reflexivity|].
symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* A MAP_NORESERVE map (YK0x.v:85-86): the map, then its lazy interior. *)
Lemma lazy_in_maps_noreserve_cf : forall a n md, lazy_in_maps_cf md ->
bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> lazy_in_maps_cf (YK0x.mmap_model_noreserve a n md).
Proof.
intros a n md H Hb. unfold YK0x.mmap_model_noreserve.
apply lazy_in_maps_add_lazy_cf; [apply lazy_in_maps_mmap_cf; exact H | exact Hb | apply lim_mmap_range].
Qed.

(* munmap_model (YK0v.v:86) drops every mapping based at addr and subtracts [addr, addr + n) from both lists;
   it keeps the field when every mapping based at addr ends inside [addr, addr + n). *)
(* Theorem Labs, 2026-11-06 (LPS 75d69e0079f9): munmap_model's vm_maps component became
   maps_subtract, so the munmap keep below has to carry a covered point from a list to that
   list's subtraction.  YK0g.maps_subtract_sem would do it but wants ivs_wf of vm_maps, which
   lazy_in_maps_munmap_cf does not have and cannot gain without moving twelve positional call
   sites.  It is not needed: iv_wf would only buy the right remnant's Z_to_bv round trip, and
   there x bounds both of its components on its own. *)
Lemma lim_cov_range : forall l x, YK0g.ivs_wf l -> YK0g.covered l x = true -> 0 <= x < 2 ^ 64.
Proof.
intros l x W C. unfold YK0g.covered in C. apply existsb_exists in C as (c & Hc & Hi). cbv beta in Hi.
pose proof (W c Hc) as Hw. unfold YK0g.iv_wf in Hw. pose proof (YK0g.B_range c) as Hb.
unfold YK0g.in_iv, YK0g.in_rng in Hi. apply andb_true_iff in Hi as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma lim_cov_subtract_keep : forall l lo hi x, 0 <= x < 2 ^ 64 ->
YK0g.in_rng lo hi x = false -> YK0g.covered l x = true ->
YK0g.covered (maps_subtract l lo hi) x = true.
Proof.
intros l lo hi x Hx HO. induction l as [|c l IH].
- intros C. discriminate C.
- intros C. destruct c as [a sz]. rewrite lim_cov_cons in C. cbn [maps_subtract].
  rewrite lim_cov_app. apply orb_true_iff.
  apply orb_true_iff in C as [C|C]; [left|right; exact (IH C)].
  unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S in C. cbn [fst snd] in C.
  apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs.
  unfold bv_modulus in Ra, Rs.
  unfold YK0g.in_rng in HO. apply andb_false_iff in HO as [O|O];
    [apply Z.leb_gt in O | apply Z.ltb_ge in O].
  + (* x < lo: the left remnant keeps x *)
    assert (EL : (bv_unsigned a <? lo)%Z = true) by (apply Z.ltb_lt; lia).
    assert (RT : bv_unsigned (Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a)))
                 = Z.min (bv_unsigned sz) (lo - bv_unsigned a)) by (apply YK0g.fg_lit; lia).
    unfold YK0g.covered. apply existsb_exists.
    exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a))).
    split; [unfold iv_subtract; cbv zeta; rewrite EL; apply in_or_app; left; left; reflexivity|].
    cbv beta. unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. cbn [fst snd]. rewrite RT.
    apply andb_true_iff. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  + (* hi <= x: the right remnant keeps x *)
    assert (ER : (hi <? bv_unsigned a + bv_unsigned sz)%Z = true) by (apply Z.ltb_lt; lia).
    assert (RB : bv_unsigned (Z_to_bv 64 (Z.max (bv_unsigned a) hi))
                 = Z.max (bv_unsigned a) hi) by (apply YK0g.fg_lit; lia).
    assert (RS : bv_unsigned (Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi))
                 = bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)
      by (apply YK0g.fg_lit; lia).
    unfold YK0g.covered. apply existsb_exists.
    exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi),
            Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)).
    split; [unfold iv_subtract; cbv zeta; rewrite ER; apply in_or_app; right; left; reflexivity|].
    cbv beta. unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. cbn [fst snd]. rewrite RB, RS.
    apply andb_true_iff. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

Lemma lazy_in_maps_munmap_cf : forall addr n md, lazy_in_maps_cf md ->
YK0g.ivs_wf (vm_noaccess (m_vmmaps md)) -> YK0g.ivs_wf (m_vm_lazy md) ->
(forall c, In c (vm_maps (m_vmmaps md)) -> fst c = addr -> bv_unsigned (snd c) <= bv_unsigned n) ->
lazy_in_maps_cf (munmap_model addr n md).
Proof.
intros addr n md H Wn Wl Hlen x Hx.
assert (Hlh : bv_unsigned addr <= bv_unsigned addr + bv_unsigned n) by (pose proof (bv_unsigned_in_range 64 n); lia).
change (YK0g.covered (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
  ++ maps_subtract (m_vm_lazy md) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) x = true) in Hx.
change (YK0g.covered (maps_subtract (vm_maps (m_vmmaps md)) (bv_unsigned addr)
  (bv_unsigned addr + bv_unsigned n)) x = true).
rewrite lim_cov_app, (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wn Hlh))),
  (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wl Hlh))) in Hx.
assert (OUT : YK0g.in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x = false).
{ destruct (YK0g.in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x); [|reflexivity].
  cbn [negb] in Hx. rewrite !andb_false_r in Hx. discriminate Hx. }
assert (IN : YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true).
{ rewrite lim_cov_app. apply orb_true_iff in Hx as [Hx|Hx]; apply andb_true_iff in Hx as [Hx _]; rewrite Hx;
  [reflexivity | apply orb_true_r]. }
(* Hlen is no longer used: with maps_subtract an entry based at addr is cut rather than
   dropped, so x being outside [addr, addr + n) is the whole argument.  The hypothesis stays
   in the statement so that none of the twelve call sites moves. *)
apply lim_cov_subtract_keep; [ | exact OUT | exact (H x IN) ].
exact (lim_cov_range _ x (YK0g.ivs_wf_app _ _ Wn Wl) IN).
Qed.

(* ---- New keeps (the kit owner's measured gaps, 2026-10-30). ---- *)

(* The prot-0 twin of lim_mmap_range: noaccess_model (YK13.v:192-197) conses (a, n) onto vm_maps too. *)
Lemma lim_noaccess_range : forall a n md x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n ->
YK0g.covered (vm_maps (m_vmmaps (YK13.noaccess_model a n md))) x = true.
Proof.
intros a n md x Hx. change (YK0g.covered (vm_maps (m_vmmaps (mmap_model a n md))) x = true).
exact (lim_mmap_range a n md x Hx).
Qed.

(* A point covered by a range subtraction of a well-formed list is covered by the list. *)
Lemma lim_cov_subtract_sub : forall l lo hi x, YK0g.ivs_wf l -> lo <= hi ->
YK0g.covered (maps_subtract l lo hi) x = true -> YK0g.covered l x = true.
Proof.
intros l lo hi x W Hlh Hx. rewrite (proj2 (proj2 (YK0g.maps_subtract_sem l lo hi W Hlh))) in Hx.
apply andb_true_iff in Hx as [Hx _]. exact Hx.
Qed.

(* The same for brk's fold of subtractions (Mmap.v maps_subtract_ranges). *)
Lemma lim_subtract_ranges_sub : forall rs l x, YK0g.ivs_wf l ->
YK0g.covered (maps_subtract_ranges l rs) x = true -> YK0g.covered l x = true.
Proof.
induction rs as [|p rs IH]; intros l x W Hx; [exact Hx|].
pose proof (bv_unsigned_in_range 64 (snd p)) as Rp.
assert (Hlh : bv_unsigned (fst p) <= bv_unsigned (fst p) + bv_unsigned (snd p)) by lia.
change (YK0g.covered (maps_subtract_ranges
  (maps_subtract l (bv_unsigned (fst p)) (bv_unsigned (fst p) + bv_unsigned (snd p))) rs) x = true) in Hx.
exact (lim_cov_subtract_sub _ _ _ x W Hlh (IH _ x (YK0g.maps_subtract_wf _ _ _ W Hlh) Hx)).
Qed.

(* forget_vm_ranges (Mmap.v) changes only the backing: vm maps unchanged, lazy list only shrinks. *)
Lemma lim_forget_ranges_vmmaps : forall rs md, m_vmmaps (forget_vm_ranges rs md) = m_vmmaps md.
Proof. induction rs as [|[a n] rs IH]; intros md; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. Qed.

Lemma lim_forget_ranges_lazy : forall rs md x, YK0g.ivs_wf (m_vm_lazy md) ->
YK0g.covered (m_vm_lazy (forget_vm_ranges rs md)) x = true -> YK0g.covered (m_vm_lazy md) x = true.
Proof.
induction rs as [|[a n] rs IH]; intros md x W Hx; [exact Hx|].
cbn [forget_vm_ranges] in Hx. pose proof (bv_unsigned_in_range 64 n) as Rn.
assert (Hlh : bv_unsigned a <= bv_unsigned a + bv_unsigned n) by lia.
assert (W' : YK0g.ivs_wf (m_vm_lazy (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) md)))
  by exact (YK0g.maps_subtract_wf _ _ _ W Hlh).
pose proof (IH _ x W' Hx) as H1.
change (YK0g.covered (maps_subtract (m_vm_lazy md) (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) x = true) in H1.
exact (lim_cov_subtract_sub _ _ _ x W Hlh H1).
Qed.

(* mprotect_model (YK13.v:245-249): maps and lazy list unchanged, [addr, addr + n) leaves the noaccess list. *)
Lemma lazy_in_maps_mprotect_cf : forall addr n md, lazy_in_maps_cf md ->
YK0g.ivs_wf (vm_noaccess (m_vmmaps md)) -> lazy_in_maps_cf (YK13.mprotect_model addr n md).
Proof.
intros addr n md H Wn x Hx.
assert (Hlh : bv_unsigned addr <= bv_unsigned addr + bv_unsigned n) by (pose proof (bv_unsigned_in_range 64 n); lia).
change (YK0g.covered (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
  ++ m_vm_lazy md) x = true) in Hx.
change (YK0g.covered (vm_maps (m_vmmaps md)) x = true).
apply H. rewrite lim_cov_app in Hx |- *. apply orb_true_iff in Hx as [Hx|Hx].
- rewrite (lim_cov_subtract_sub _ _ _ x Wn Hlh Hx). reflexivity.
- rewrite Hx. apply orb_true_r.
Qed.


(* ---- Equation forms of YA09's post records (the kit owner, 2026-10-30 07:12Z; YA09 / YA0e lines below). Each
   takes the record's own field equations as hypotheses (a YA* function in a field is a bool parameter), so YA09's
   builders can call it. YA0e.v:36 in_ivs z l is YK0g.covered l z by conversion: these apply to in_ivs goals. ---- *)

Lemma lim_in_iv_range : forall (a n : word) x, YK0g.in_iv (a, n) x = true ->
bv_unsigned a <= x < bv_unsigned a + bv_unsigned n.
Proof.
intros a n x H. unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S in H. cbn [fst snd] in H.
apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* grant_post (YA09.v:1716): gp_maps (:1717) and gp_lazy (:1720, lz := kind_lazy kd). At grant_cs1_ok (YA09.v:1903):
   lzsub_grant_post_eq (kind_lazy kd) a n model model' (gp_maps _ _ _ _ _ GPo) (gp_lazy _ _ _ _ _ GPo) Hsub. *)
Lemma lzsub_grant_post_eq : forall (lz : bool) (a n : word) model model',
vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model) ->
m_vm_lazy model' = (if lz then (a, n) :: m_vm_lazy model else m_vm_lazy model) ->
(forall z, YK0g.covered (m_vm_lazy model) z = true -> YK0g.covered (vm_maps (m_vmmaps model)) z = true) ->
forall z, YK0g.covered (m_vm_lazy model') z = true -> YK0g.covered (vm_maps (m_vmmaps model')) z = true.
Proof.
intros lz a n model model' Em El H z Hz. rewrite Em, lim_cov_cons. rewrite El in Hz.
destruct lz; [rewrite lim_cov_cons in Hz; apply orb_true_iff in Hz as [Hz|Hz]; [rewrite Hz; reflexivity|]|];
rewrite (H z Hz); apply orb_true_r.
Qed.

(* The same with the noaccess list: gp_maps (:1717), gp_noacc (:1719, nb := kind_none kd), gp_lazy (:1720).
   lazy_in_maps_grant_post_eq_cf (kind_none kd) (kind_lazy kd) a n model model' (gp_maps _ _ _ _ _ GPo)
   (gp_noacc _ _ _ _ _ GPo) (gp_lazy _ _ _ _ _ GPo) H. *)
Lemma lazy_in_maps_grant_post_eq_cf : forall (nb lz : bool) (a n : word) model model',
vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model) ->
vm_noaccess (m_vmmaps model') = (if nb then (a, n) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model)) ->
m_vm_lazy model' = (if lz then (a, n) :: m_vm_lazy model else m_vm_lazy model) ->
lazy_in_maps_cf model -> lazy_in_maps_cf model'.
Proof.
intros nb lz a n model model' Em En El H x Hx. rewrite Em, lim_cov_cons.
rewrite lim_cov_app, En, El in Hx. apply orb_true_iff in Hx as [Hx|Hx].
- assert (Hn : YK0g.in_iv (a, n) x = true \/ YK0g.covered (vm_noaccess (m_vmmaps model)) x = true).
  { destruct nb; [rewrite lim_cov_cons in Hx; apply orb_true_iff; exact Hx | right; exact Hx]. }
  destruct Hn as [Hn|Hn]; [rewrite Hn; reflexivity|].
  assert (IN : YK0g.covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true)
    by (rewrite lim_cov_app, Hn; reflexivity).
  rewrite (H x IN). apply orb_true_r.
- assert (Hl : YK0g.in_iv (a, n) x = true \/ YK0g.covered (m_vm_lazy model) x = true).
  { destruct lz; [rewrite lim_cov_cons in Hx; apply orb_true_iff; exact Hx | right; exact Hx]. }
  destruct Hl as [Hl|Hl]; [rewrite Hl; reflexivity|].
  assert (IN : YK0g.covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true)
    by (rewrite lim_cov_app, Hl; apply orb_true_r).
  rewrite (H x IN). apply orb_true_r.
Qed.

(* slice_post (YA09.v:3125): sp_maps (:3126) and sp_lazy (:3131-3136). sp_lazy matches on YA09's slarm, so its
   three outcomes enter as a disjunction (SlM | SlF | SlE, SlG). At slice_cs1_ok (YA09.v:3342, after its
   `destruct s0; rewrite <- Es`): lzsub_slice_post_eq addr n model model' (sp_maps _ _ _ _ _ SPo) LZ W3 RNG Hsub,
   LZ from sp_lazy _ _ _ _ _ SPo per arm, RNG from sl_in_maps (YA09.v:3202; word-quantified: lim_range_words). *)
Lemma lzsub_slice_post_eq : forall (addr n : word) model model',
vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model) ->
(m_vm_lazy model' = m_vm_lazy model
 \/ m_vm_lazy model' = (addr, n) :: maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
 \/ m_vm_lazy model' = maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) ->
YK0g.ivs_wf (m_vm_lazy model) ->
(forall x, bv_unsigned addr <= x < bv_unsigned addr + bv_unsigned n -> YK0g.covered (vm_maps (m_vmmaps model)) x = true) ->
(forall z, YK0g.covered (m_vm_lazy model) z = true -> YK0g.covered (vm_maps (m_vmmaps model)) z = true) ->
forall z, YK0g.covered (m_vm_lazy model') z = true -> YK0g.covered (vm_maps (m_vmmaps model')) z = true.
Proof.
intros addr n model model' Em El Wl Hr H z Hz. rewrite Em.
assert (Hlh : bv_unsigned addr <= bv_unsigned addr + bv_unsigned n) by (pose proof (bv_unsigned_in_range 64 n); lia).
destruct El as [El|[El|El]]; rewrite El in Hz.
- exact (H z Hz).
- rewrite lim_cov_cons in Hz. apply orb_true_iff in Hz as [Hz|Hz].
  + exact (Hr z (lim_in_iv_range addr n z Hz)).
  + exact (H z (lim_cov_subtract_sub _ _ _ z Wl Hlh Hz)).
- exact (H z (lim_cov_subtract_sub _ _ _ z Wl Hlh Hz)).
Qed.

(* The same with the noaccess list: sp_maps (:3126), sp_noacc (:3128-3130, nn := sl_nn s), sp_lazy as above.
   lazy_in_maps_slice_post_eq_cf (sl_nn s) addr n model model' (sp_maps _ _ _ _ _ SPo) (sp_noacc _ _ _ _ _ SPo)
   LZ W2 W3 RNG H. *)
Lemma lazy_in_maps_slice_post_eq_cf : forall (nn : bool) (addr n : word) model model',
vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model) ->
vm_noaccess (m_vmmaps model') = (if nn then [(addr, n)] else [])
  ++ maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ->
(m_vm_lazy model' = m_vm_lazy model
 \/ m_vm_lazy model' = (addr, n) :: maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
 \/ m_vm_lazy model' = maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) ->
YK0g.ivs_wf (vm_noaccess (m_vmmaps model)) -> YK0g.ivs_wf (m_vm_lazy model) ->
(forall x, bv_unsigned addr <= x < bv_unsigned addr + bv_unsigned n -> YK0g.covered (vm_maps (m_vmmaps model)) x = true) ->
lazy_in_maps_cf model -> lazy_in_maps_cf model'.
Proof.
intros nn addr n model model' Em En El Wn Wl Hr H x Hx. rewrite Em.
assert (Hlh : bv_unsigned addr <= bv_unsigned addr + bv_unsigned n) by (pose proof (bv_unsigned_in_range 64 n); lia).
rewrite lim_cov_app in Hx. apply orb_true_iff in Hx as [Hx|Hx].
- rewrite En, lim_cov_app in Hx. apply orb_true_iff in Hx as [Hx|Hx].
  + destruct nn; [rewrite lim_cov_cons in Hx; apply orb_true_iff in Hx as [Hx|Hx];
      [exact (Hr x (lim_in_iv_range addr n x Hx))|]|]; cbn in Hx; discriminate Hx.
  + apply H. rewrite lim_cov_app, (lim_cov_subtract_sub _ _ _ x Wn Hlh Hx). reflexivity.
- destruct El as [El|[El|El]]; rewrite El in Hx.
  + apply H. rewrite lim_cov_app, Hx. apply orb_true_r.
  + rewrite lim_cov_cons in Hx. apply orb_true_iff in Hx as [Hx|Hx]; [exact (Hr x (lim_in_iv_range addr n x Hx))|].
    apply H. rewrite lim_cov_app, (lim_cov_subtract_sub _ _ _ x Wl Hlh Hx). apply orb_true_r.
  + apply H. rewrite lim_cov_app, (lim_cov_subtract_sub _ _ _ x Wl Hlh Hx). apply orb_true_r.
Qed.

(* sl_in_maps (YA09.v:3202) quantifies over words; this gives the Z-quantified range premise above from it. *)
Lemma lim_range_words : forall (a n : word) l, bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> YK0g.covered l (bv_unsigned x) = true) ->
forall x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n -> YK0g.covered l x = true.
Proof.
intros a n l Hb H x Hx. pose proof (bv_unsigned_in_range 64 a) as Ra.
pose proof (YK0g.fg_lit x ltac:(lia)) as E. rewrite <- E. apply H. rewrite E. exact Hx.
Qed.

(* dest_post (YA09.v:3646): dp_maps (:3647) and dp_lazy (:3650). At dest_cs1_ok (YA09.v:3789):
   lzsub_dest_post_eq addr n model model' (dp_maps _ _ _ _ DPo) (dp_lazy _ _ _ _ DPo) W1 W3 Hsub. *)
Lemma lzsub_dest_post_eq : forall (addr n : word) model model',
vm_maps (m_vmmaps model') = maps_subtract (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ->
m_vm_lazy model' = maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ->
YK0g.ivs_wf (vm_maps (m_vmmaps model)) -> YK0g.ivs_wf (m_vm_lazy model) ->
(forall z, YK0g.covered (m_vm_lazy model) z = true -> YK0g.covered (vm_maps (m_vmmaps model)) z = true) ->
forall z, YK0g.covered (m_vm_lazy model') z = true -> YK0g.covered (vm_maps (m_vmmaps model')) z = true.
Proof.
intros addr n model model' Em El Wm Wl H z Hz.
assert (Hlh : bv_unsigned addr <= bv_unsigned addr + bv_unsigned n) by (pose proof (bv_unsigned_in_range 64 n); lia).
rewrite El, (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wl Hlh))) in Hz.
rewrite Em, (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wm Hlh))).
apply andb_true_iff in Hz as [Hz Ho]. rewrite (H z Hz), Ho. reflexivity.
Qed.

(* The same with the noaccess list: dp_maps (:3647), dp_noacc (:3649), dp_lazy (:3650). It is also the keep of
   YA05.v:656 fixedin_destroyed_model (whose three equations hold by reflexivity), which this file cannot name.
   lazy_in_maps_dest_post_eq_cf addr n model model' (dp_maps _ _ _ _ DPo) (dp_noacc _ _ _ _ DPo)
   (dp_lazy _ _ _ _ DPo) W1 W2 W3 H. *)
Lemma lazy_in_maps_dest_post_eq_cf : forall (addr n : word) model model',
vm_maps (m_vmmaps model') = maps_subtract (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ->
vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ->
m_vm_lazy model' = maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ->
YK0g.ivs_wf (vm_maps (m_vmmaps model)) -> YK0g.ivs_wf (vm_noaccess (m_vmmaps model)) -> YK0g.ivs_wf (m_vm_lazy model) ->
lazy_in_maps_cf model -> lazy_in_maps_cf model'.
Proof.
intros addr n model model' Em En El Wm Wn Wl H x Hx.
assert (Hlh : bv_unsigned addr <= bv_unsigned addr + bv_unsigned n) by (pose proof (bv_unsigned_in_range 64 n); lia).
rewrite En, El, lim_cov_app, (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wn Hlh))),
  (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wl Hlh))) in Hx.
rewrite Em, (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wm Hlh))).
assert (OUT : negb (YK0g.in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x) = true).
{ apply orb_true_iff in Hx as [Hx|Hx]; apply andb_true_iff in Hx as [_ Hx]; exact Hx. }
assert (IN : YK0g.covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true).
{ rewrite lim_cov_app. apply orb_true_iff in Hx as [Hx|Hx]; apply andb_true_iff in Hx as [Hx _]; rewrite Hx;
  [reflexivity | apply orb_true_r]. }
rewrite (H x IN), OUT. reflexivity.
Qed.
