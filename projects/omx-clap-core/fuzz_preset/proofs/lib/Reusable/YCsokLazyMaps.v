(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCsokLazyMaps.v, with its module paths changed; 17 of its 65 lines of code are new or changed. *)
(* Theorem Labs, 2026-10-30: what the start-up invariant cs_ok (YA0e.v, Record cs_ok) gives about the cf layer's
   lazy_in_maps (alc_lazy_in_maps: covered (vm_noaccess ++ m_vm_lazy) x = true -> covered (vm_maps) x = true) at ANY
   state it holds, so at main entry (AD2i.v / YD2i.v tfib_main_entry's HC). Proves no function (start-up facts).
   (1) cs_ok_noaccess_in_maps: the noaccess half, from co_nasub.
   (2) cs_ok_lazy_lit / cs_ok_noaccess_lit: a literal KRWLAZY map of the symbolic state puts its pages in m_vm_lazy
       (co_kinds), a literal KNONE / KNONELAZY map puts its interval in vm_noaccess (co_none). No file of this tree
       applies them; the start-up rows read co_lzsub through (4) (lib/A/PresetD1pAPfC.v, lib/AU/PresetStartRowsB.v).
   (3) cs_ok_lazy_half_in_maps: the lazy half, from co_lzsub (YA0e.v), the field cs_ok carries for it. co_lzsub is
       proved at init (YA02.v init_cs_ok, init_cs_ok_g, init_cs_ok_zero, by YKlazy.lazy_in_maps_init_cf) and kept by
       every builder of cs_ok that changes m_vm_lazy or vm_maps (YA08.v brk-grow and munmap arms, YA09.v
       grant_cs1_ok, slice_cs1_ok, dest_cs1_ok, each by a YKlazy keep lemma); the other builders leave both alone.
   (4) cs_ok_lazy_in_maps_cf: lazy_in_maps itself, both halves (noaccess and lazy) in YK0g.covered form. Its
       proof splits the covered list (existsb_app) and closes the noaccess half by co_nasub and the lazy half by
       co_lzsub, the two cs_ok fields of YA0e.v; its conclusion is
       ARcf_nil_init's inline premise (lib/Reusable/YGcfNilInit.v, its alc_lazy_in_maps premise) token for
       token, md renamed model, and the body of the cf layer's YKlazy.lazy_in_maps_cf (lib/Reusable/YKlazy.v, by path
       from the cf layer). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK00 YK0c YK0e YK09 YK0g YA0c YA0e.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import APSG.
Open Scope Z_scope.

Lemma covered_in_ivs : forall (C : list (word * word)) (x : Z), YK0g.covered C x = in_ivs x C.
Proof. reflexivity. Qed.

(* (1) the noaccess half of lazy_in_maps, at every cs_ok state *)
Theorem cs_ok_noaccess_in_maps : forall SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model,
cs_ok SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model ->
forall x, YK0g.covered (vm_noaccess (m_vmmaps model)) x = true -> YK0g.covered (vm_maps (m_vmmaps model)) x = true.
Proof.
intros SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model HC x Hx.
rewrite covered_in_ivs in Hx |- *. exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC x Hx).
Qed.

(* (3) the lazy half of lazy_in_maps, at every cs_ok state *)
Theorem cs_ok_lazy_half_in_maps : forall SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model,
cs_ok SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model ->
forall x, YK0g.covered (m_vm_lazy model) x = true -> YK0g.covered (vm_maps (m_vmmaps model)) x = true.
Proof.
intros SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model HC x Hx.
rewrite covered_in_ivs in Hx |- *. exact (co_lzsub _ _ _ _ _ _ _ _ _ _ _ _ HC x Hx).
Qed.

(* (4) lazy_in_maps, at every cs_ok state: both halves, the cf layer's lazy_in_maps_cf unfolded (YKlazy.v) *)
Theorem cs_ok_lazy_in_maps_cf : forall SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model,
  cs_ok SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model ->
  forall x, YK0g.covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true ->
  YK0g.covered (vm_maps (m_vmmaps model)) x = true.
Proof.
intros SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model HC x Hx.
unfold YK0g.covered in Hx. rewrite existsb_app in Hx. apply orb_prop in Hx as [Hx|Hx].
- exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC x Hx).
- exact (co_lzsub _ _ _ _ _ _ _ _ _ _ _ _ HC x Hx).
Qed.

(* (2) literal maps of the symbolic state, read into the model's ledgers *)
Definition amap_eqb (m m' : amap) : bool :=
(expr_eqb (am_base m) (am_base m') && expr_eqb (am_len m) (am_len m') && mkind_eqb (am_kind m) (am_kind m'))%bool.
Lemma amap_eqb_eq : forall m m', amap_eqb m m' = true -> m = m'.
Proof.
intros [b n k] [b' n' k'] H. unfold amap_eqb in H. cbn [am_base am_len am_kind] in H.
apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hb Hn].
apply expr_eqb_eq in Hb. apply expr_eqb_eq in Hn. apply mkind_eqb_eq in Hk. subst. reflexivity.
Qed.
Lemma amap_in_of_existsb : forall m l, existsb (amap_eqb m) l = true -> In m l.
Proof.
intros m l H. apply existsb_exists in H as (m' & Hin & He). apply amap_eqb_eq in He. subst. exact Hin.
Qed.

Theorem cs_ok_lazy_lit : forall SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model (b n : Z),
cs_ok SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model ->
In (AM (ELit b) (ELit n) KRWLAZY) (a_maps cs) ->
0 <= b -> 0 < n -> b + n < 2 ^ 64 ->
page_in_ranges (page_base (Z_to_bv 64 b)) (m_vm_lazy model) = true.
Proof.
intros SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model b n HC Hin Hb Hn Hbn.
pose proof (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin eq_refl (Z_to_bv 64 b)) as K.
cbn [am_base am_len edenot] in K. rewrite !u64_lit in K by lia.
exact (proj2 (K ltac:(lia))).
Qed.

Theorem cs_ok_noaccess_lit : forall SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model (b n : Z) kd,
cs_ok SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model ->
In (AM (ELit b) (ELit n) kd) (a_maps cs) -> kd = KNONE \/ kd = KNONELAZY ->
In (Z_to_bv 64 b, Z_to_bv 64 n) (vm_noaccess (m_vmmaps model)).
Proof.
intros SEGS A LIMIT TOP SINV argH FS0 E cs R FULL model b n kd HC Hin Hkd.
exact (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin Hkd).
Qed.
