(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl MI_WGroup.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Record rgeom := mkRG { rg_g : aptr; rg_idx : Z; rg_stride : Z; rg_start : Z; rg_end : Z }.

Definition realloc_geom (cs : mstate) (c : cptr) : option rgeom :=
  match (s_slots cs) !! c with
  | Some (g, idx) =>
      let stride := get_stride (get_meta_rec cs g) in
      let start := conc cs c in
      Some (mkRG g idx stride start (start + stride - IB))
  | None => None
  end.

Definition inplace_ok (cs : mstate) (rg : rgeom) (A n : Z) : bool :=
  (n <=? rg_end rg - A) && (n <? MMAP_THRESHOLD) && (m_sizeclass (get_meta_rec cs (rg_g rg)) <=? size_to_class n + 1).

Definition remap_needed (base n : Z) : Z := (n + base + UNIT + IB + 4095) / 4096 * 4096.

Inductive rcase : Type :=
| RcInPlace
| RcRemap (rid : N) (g : aptr) (oldb oldl needed : Z)
| RcMove.

Definition realloc_case (cs : mstate) (c : cptr) (A n : Z) : rcase :=
  match realloc_geom cs c with
  | None => RcMove
  | Some rg =>
      if inplace_ok cs rg A n then RcInPlace
      else
        let mr := get_meta_rec cs (rg_g rg) in
        if (MMAP_THRESHOLD <=? n) && (48 <=? m_sizeclass mr) then
          RcRemap (fst c) (rg_g rg)
                  (match m_mem mr with Some bm => conc cs bm | None => 0 end)
                  (m_maplen mr * 4096)
                  (remap_needed (A - rg_start rg) n)
        else RcMove
  end.

Definition remap_update (cs : mstate) (rid : N) (g : aptr) (nb needed : Z) : mstate :=
  upd_meta g (m_set_maplen (needed / 4096))
           (set_regions (<[rid := mkRegion RKGroup nb needed]> (s_regions cs)) cs).

Definition live_ranges_except (cs : mstate) (rid : N) : list (Z * Z) :=
  s_reserved cs ++ map (fun kr : N * region => region_live_range (snd kr))
                       (filter (fun kr : N * region => negb (N.eqb (fst kr) rid)) (map_to_list (s_regions cs))).

Lemma remap_needed_pg base n : remap_needed base n mod 4096 = 0.
Proof. unfold remap_needed. rewrite Z.mul_comm, Z.mul_mod by lia. reflexivity. Qed.

Lemma remap_needed_ge base n : 0 <= n -> 0 <= base -> n + base + UNIT + IB <= remap_needed base n < n + base + UNIT + IB + 4096.
Proof. intros Hn Hb. unfold remap_needed, UNIT, IB. Z.div_mod_to_equations. lia. Qed.

Lemma strip_remap_update cs rid g nb needed :
  strip (remap_update cs rid g nb needed) = remap_update (strip cs) rid g nb needed.
Proof. reflexivity. Qed.

Lemma s_slots_remap_update cs rid g nb needed : s_slots (remap_update cs rid g nb needed) = s_slots cs.
Proof. reflexivity. Qed.
Lemma s_groups_remap_update cs rid g nb needed : s_groups (remap_update cs rid g nb needed) = s_groups cs.
Proof. reflexivity. Qed.
Lemma s_areas_remap_update cs rid g nb needed : s_areas (remap_update cs rid g nb needed) = s_areas cs.
Proof. reflexivity. Qed.
Lemma s_ctx_remap_update cs rid g nb needed : s_ctx (remap_update cs rid g nb needed) = s_ctx cs.
Proof. reflexivity. Qed.
Lemma s_regions_remap_update cs rid g nb needed :
  s_regions (remap_update cs rid g nb needed) = <[rid := mkRegion RKGroup nb needed]> (s_regions cs).
Proof. reflexivity. Qed.

Definition ss_list (p e : aptr) (n i : Z) : list (aptr * Z) :=
  let res := snd e - snd p - n in
  (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
  ++ (if 5 <=? res then [(aadd e (-5), 0); (aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8);
                         (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24)] else [])
  ++ [(aadd p (-3), i + 32 * Z.min res 5)].

Definition inplace_full (st : mstate) (c : cptr) (off n : Z) : mstate :=
  match (s_slots st) !! c with
  | Some (g, idx) =>
      let st0 := set_tick (N.succ (s_tick st)) st in
      let stride := get_stride (get_meta_rec st g) in
      let p := aadd c (UNIT * off) in
      let e := aadd c (stride - IB) in
      havoc p n (wrs (ss_list p e n idx) st0)
  | None => st
  end.

Definition trim_cells (k : Z) (cs : gmap Z (Z * N)) : gmap Z (Z * N) :=
  filter (fun kv : Z * (Z * N) => kv.1 < k) cs.
Definition trim_shadow (rid : N) (k : Z) (st : mstate) : mstate :=
  upd_shadow rid (fun sh => mkShadow (trim_cells k (r_cells sh)) (r_hav sh) (r_havp sh)) st.

Definition remap_full (st : mstate) (c : cptr) (off n nb needed : Z) : mstate :=
  match (s_slots st) !! c with
  | Some (g, idx) =>
      let oldl := m_maplen (get_meta_rec st g) * 4096 in
      let st0 := set_tick (N.succ (s_tick st)) (trim_shadow (fst c) (Z.min oldl needed) (remap_update st (fst c) g nb needed)) in
      let stride := get_stride (get_meta_rec st0 g) in
      let p := aadd c (UNIT * off) in
      let e := aadd c (stride - IB) in
      havoc p n (wrs (ss_list p e n idx) (wr8 e 0 st0))
  | None => st
  end.

Lemma strip_wrs l st : strip (wrs l st) = strip st.
Proof. revert st. induction l as [|[q v] l IH]; intros st; cbn; [reflexivity|]. rewrite IH. apply strip_wr8. Qed.

Lemma strip_inplace_full st c off n : strip (inplace_full st c off n) = strip st.
Proof.
  unfold inplace_full. destruct (s_slots st !! c) as [[g idx]|]; [| reflexivity].
  rewrite strip_havoc, strip_wrs, strip_set_tick. reflexivity.
Qed.

Lemma strip_trim_shadow rid k st : strip (trim_shadow rid k st) = strip st.
Proof. reflexivity. Qed.

Lemma strip_remap_full st c off n nb needed :
  (exists gi, (s_slots st) !! c = Some gi) ->
  strip (remap_full st c off n nb needed) = remap_update (strip st) (fst c) (match (s_slots st) !! c with Some (g, _) => g | None => c end) nb needed.
Proof.
  intros [[g idx] Hs]. unfold remap_full. rewrite Hs. rewrite strip_havoc, strip_wrs, strip_wr8, strip_set_tick, strip_trim_shadow. apply strip_remap_update.
Qed.

End CEIL.
