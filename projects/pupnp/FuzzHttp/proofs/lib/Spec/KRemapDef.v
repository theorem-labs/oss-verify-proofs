(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger.
Import ListNotations.
Local Open Scope Z_scope.

Definition rebase_regions (st : mstate) (rid : N) (dst nn : Z) : mstate :=
  set_regions (<[rid := mkRegion RKGroup dst nn]> (s_regions st)) st.

Definition rebase_ctrl (st : mstate) (rid : N) (g : aptr) (dst nn : Z) : mstate :=
  upd_meta g (m_set_maplen (nn / 4096)) (rebase_regions st rid dst nn).

Definition cremap (cs : mstate) (rid : N) (g : aptr) (dst nn : Z) : mstate := rebase_ctrl cs rid g dst nn.

Definition lremap (L : mled) (b dst nn : Z) : mled := set_groups ((dst, nn) :: g_remove b (ld_groups L)) L.

Lemma lremap_live L b dst nn : ld_live (lremap L b dst nn) = ld_live L.
Proof. reflexivity. Qed.
Lemma lremap_resv L b dst nn : ld_resv (lremap L b dst nn) = ld_resv L.
Proof. reflexivity. Qed.

Definition cremap_ok (cs : mstate) (c : cptr) (dst nn : Z) : Prop :=
  0 < dst /\ dst mod PGSZ = 0 /\ nn mod PGSZ = 0 /\ 2 * PGSZ <= nn /\ nn < LEN_MAX /\ dst + nn <= s_ceil cs
  /\ ranges_free (s_reserved cs) dst nn = true
  /\ (forall rid2 r2, s_regions cs !! rid2 = Some r2 -> rid2 <> fst c ->
        let '(b2, l2) := region_live_range r2 in dst + nn <= b2 \/ b2 + l2 <= dst).

Inductive creach2 : mstate -> mled -> Prop :=
| c2_init resv ceil : ceil <= alloc_ceiling_max -> creach2 (strip (minit 0 resv ceil)) (led_init resv ceil)
| c2_malloc cs L n L' cs' r :
    creach2 cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
    creach2 cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| c2_free cs L c L' cs' :
    creach2 cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
    creach2 cs' (set_live (ap_remove c (ld_live L')) L')
| c2_remap cs L c g rg dst nn :
    creach2 cs L -> In c (ld_live L) ->
    s_slots cs !! c = Some (g, 0) -> m_sizeclass (get_meta_rec cs g) = 63 -> s_regions cs !! fst c = Some rg ->
    cremap_ok cs c dst nn ->
    creach2 (cremap cs (fst c) g dst nn) (set_live (c :: ap_remove c (ld_live L)) (lremap L (r_base rg) dst nn)).

Lemma creach_creach2 cs L : creach cs L -> creach2 cs L.
Proof.
  induction 1.
  - apply c2_init. assumption.
  - eapply c2_malloc; eauto.
  - eapply c2_free; eauto.
Qed.
