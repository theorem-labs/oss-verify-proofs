(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YKlazy.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YKlazy.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YK0v YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0g YK13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK02.
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
End k.

(* The init witness: the process's first model has no noaccess and no lazy range. *)
Lemma lazy_in_maps_init_cf : forall md, vm_noaccess (m_vmmaps md) = [] -> m_vm_lazy md = [] -> lazy_in_maps_cf md.
Proof. intros md E1 E2 x Hx. rewrite E1, E2 in Hx. cbn in Hx. discriminate Hx. Qed.

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

(* A point covered by a range subtraction of a well-formed list is covered by the list. *)
Lemma lim_cov_subtract_sub : forall l lo hi x, YK0g.ivs_wf l -> lo <= hi ->
YK0g.covered (maps_subtract l lo hi) x = true -> YK0g.covered l x = true.
Proof.
intros l lo hi x W Hlh Hx. rewrite (proj2 (proj2 (YK0g.maps_subtract_sem l lo hi W Hlh))) in Hx.
apply andb_true_iff in Hx as [Hx _]. exact Hx.
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
