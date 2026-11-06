(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2B. Import APC.
Unset Lia Cache.
Open Scope Z_scope.

Module YN.
Section WithSegs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.

(* [comment removed for export] *)
Fixpoint shdisj_all (cs : acs) (b0 n0 : expr) (ms : list amap) : acs :=
  match ms with
  | [] => cs
  | m :: rest =>
      let cs1 := if is_fog m then cs
                 else match node_shdisj A cs b0 n0 (am_base m) (am_len m) with Some cs' => cs' | None => cs end in
      shdisj_all cs1 b0 n0 rest
  end.
Definition node_shdisj_maps (cs : acs) : option acs :=
  match a_maps cs with
  | m0 :: rest => if is_fog m0 then None else Some (shdisj_all cs (am_base m0) (am_len m0) rest)
  | [] => None
  end.

(* [comment removed for export] *)
Definition node_linkrange_ref (cs : acs) (e1 e2 : expr) : option acs :=
  let k := kn cs in
  match xlo k e2, xhi k e2 with
  | Some lo, Some hi =>
      if (lin_ge0 k [(e1, 0)] [(e2, 0)] && lin_ge0 k [(e2, 0)] [(e1, 0)])%bool
      then Some (set_kn cs (KRange e1 lo hi :: k)) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_linkrange (cs : acs) (e1 e2 : expr) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  match xloB bc e2, xhiB bc e2 with
  | Some lo, Some hi =>
      if (lin_ge0B bc [(e1, 0)] [(e2, 0)] && lin_ge0B bc [(e2, 0)] [(e1, 0)])%bool
      then Some (set_kn cs (KRange e1 lo hi :: k)) else None
  | _, _ => None
  end.

Lemma node_linkrange_eq : forall cs e1 e2, node_linkrange cs e1 e2 = node_linkrange_ref cs e1 e2.
Proof.
  intros. unfold node_linkrange, node_linkrange_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint take_kzero_lit (k : list kentry) (a : Z) : option (Z * list kentry) :=
  match k with
  | [] => None
  | KZero (SA (ELit 0) o) (ELit L) :: rest =>
      if Z.eqb o a then Some (L, rest)
      else match take_kzero_lit rest a with Some (L', r') => Some (L', KZero (SA (ELit 0) o) (ELit L) :: r') | None => None end
  | K :: rest => match take_kzero_lit rest a with Some (L', r') => Some (L', K :: r') | None => None end
  end.
Definition node_splitzero (cs : acs) (a m : Z) : option acs :=
  match take_kzero_lit (kn cs) a with
  | Some (L, rest) =>
      if (Z.ltb 0 m && Z.ltb m L && Z.leb 0 a && Z.ltb L two64)%bool
      then Some (set_kn cs (KZero (SA (ELit 0) a) (ELit m) :: KZero (SA (ELit 0) (a + m)) (ELit (L - m)) :: rest))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint disj_len_scan (k allk : list kentry) (x y z : expr) (m : Z) : bool :=
  match k with
  | [] => false
  | KDisj (SA b1 o1) n1 (SA b2 o2) n2 :: rest =>
      (if (expr_eqb b1 x && Z.eqb o1 0 && expr_eqb b2 y && Z.eqb o2 0)%bool then lin_ge0 allk [(n2, 0)] [(z, m)]
       else if (expr_eqb b1 y && Z.eqb o1 0 && expr_eqb b2 x && Z.eqb o2 0)%bool then lin_ge0 allk [(n1, 0)] [(z, m)]
       else false)
      || disj_len_scan rest allk x y z m
  | _ :: rest => disj_len_scan rest allk x y z m
  end.
Definition node_disjdom_ref (cs : acs) (x y z : expr) (m : Z) : option acs :=
  let k := kn cs in
  match xhi k x, xhi k y, xhi k z with
  | Some hx, Some hy, Some hz =>
      if (Z.leb 0 m && Z.ltb (hy + hz) two64
          && (lin_ge0 k [(x, 0)] [(y, 0); (z, m)]                                          (* [comment removed for export] *)
              || (lin_ge0 k [(x, 0)] [(y, 1)] && disj_len_scan k k x y z m)))%bool          (* [comment removed for export] *)
      then Some (set_kn cs (KRange (esub x (eadd y z)) m hx :: k)) else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition node_disjdom (cs : acs) (x y z : expr) (m : Z) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  match xhiB bc x, xhiB bc y, xhiB bc z with
  | Some hx, Some hy, Some hz =>
      if (Z.leb 0 m && Z.ltb (hy + hz) two64
          && (lin_ge0B bc [(x, 0)] [(y, 0); (z, m)]                                          (* [comment removed for export] *)
              || (lin_ge0B bc [(x, 0)] [(y, 1)] && disj_len_scan k k x y z m)))%bool          (* [comment removed for export] *)
      then Some (set_kn cs (KRange (esub x (eadd y z)) m hx :: k)) else None
  | _, _, _ => None
  end.

Lemma node_disjdom_eq : forall cs x y z m, node_disjdom cs x y z m = node_disjdom_ref cs x y z m.
Proof.
  intros. unfold node_disjdom, node_disjdom_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint clip_kzero (k : list kentry) (sb : expr) (sk : Z) (Lnew : expr) (allk : list kentry) : option (list kentry) :=
  match k with
  | [] => None
  | KZero (SA b o) L :: rest =>
      if (expr_eqb b sb && Z.eqb o sk && lin_ge0 allk [(L, 0)] [(Lnew, 0)])%bool then Some (KZero (SA b o) Lnew :: rest)
      else match clip_kzero rest sb sk Lnew allk with Some r' => Some (KZero (SA b o) L :: r') | None => None end
  | K :: rest => match clip_kzero rest sb sk Lnew allk with Some r' => Some (K :: r') | None => None end
  end.
Definition node_zeroprefix (cs : acs) (b Lnew : expr) : option acs :=
  let '(sb, sk) := split_lit b in
  match clip_kzero (kn cs) sb sk Lnew (kn cs) with Some k' => Some (set_kn cs k') | None => None end.

(* [comment removed for export] *)
Definition node_srlstep (cs : acs) (x : expr) (a s : Z) : option acs :=
  let k := kn cs in
  match xhi k x with
  | Some hx =>
      if (Z.leb 0 a && Z.leb 1 s && Z.leb s 62 && Z.ltb (hx + a) two64)%bool
      then Some (set_kn cs (KRange (esub (mkSrl k (eaddz x a) s) (mkSrl k x s)) 0 ((a + 2 ^ s - 1) / 2 ^ s) :: k))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_srlrange (cs : acs) (e : expr) (s : Z) : option acs :=
  let k := kn cs in
  match erange k e with
  | Some (lo, hi) =>
      if (Z.leb 1 s && Z.leb s 62)%bool then Some (set_kn cs (KRange (mkSrl k e s) (lo / 2 ^ s) (hi / 2 ^ s) :: k)) else None
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint find_byte (k allk : list kentry) (ab : expr) (off : Z) : option expr :=
  match k with
  | [] => None
  | KWord (SA b o) 1%nat w :: rest =>
      if (expr_eqb b ab && Z.eqb o off)%bool then Some w else find_byte rest allk ab off
  | KFill (SA b o) L c :: rest =>
      if (expr_eqb b ab && Z.leb o off
          && match xlo allk L with Some lo => Z.ltb (off - o) lo | None => false end)%bool
      then Some (ELit c) else find_byte rest allk ab off
  | _ :: rest => find_byte rest allk ab off
  end.
(* [comment removed for export] *)
Definition find_byte2 (k : list kentry) (ab : expr) (ao : Z) : option expr :=
  match find_byte k k ab ao with
  | Some w => Some w
  | None => match know_byte_lit segs k ab ao with Some z => Some (ELit z) | None => None end
  end.
Definition node_bytespell_ref (cs : acs) (a : expr) (off : Z) (V : expr) : option acs :=
  let k := kn cs in
  let '(ab, ao) := split_lit (eaddz a off) in    (* [comment removed for export] *)
  match find_byte2 k ab ao with
  | Some w =>
      let w' := extK k w in
      if (flat_x k ab ao (ELit 1) && lin_ge0 k [(w', 0)] [(V, 0)] && lin_ge0 k [(V, 0)] [(w', 0)])%bool
      then Some (set_kn cs (KWord (SA ab ao) 1 V :: k)) else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_bytespell (cs : acs) (a : expr) (off : Z) (V : expr) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  let '(ab, ao) := split_lit (eaddz a off) in    (* [comment removed for export] *)
  match find_byte2 k ab ao with
  | Some w =>
      let w' := extKB bc w in
      if (flat_xB bc ab ao (ELit 1) && lin_ge0B bc [(w', 0)] [(V, 0)] && lin_ge0B bc [(V, 0)] [(w', 0)])%bool
      then Some (set_kn cs (KWord (SA ab ao) 1 V :: k)) else None
  | None => None
  end.

Lemma node_bytespell_eq : forall cs a off V, node_bytespell cs a off V = node_bytespell_ref cs a off V.
Proof.
  intros. unfold node_bytespell, node_bytespell_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint find_word (k : list kentry) (ab : expr) (off : Z) (n : nat) : option expr :=
  match k with
  | [] => None
  | KWord (SA b o) m w :: rest =>
      if (expr_eqb b ab && Z.eqb o off && Nat.eqb m n)%bool then Some w else find_word rest ab off n
  | _ :: rest => find_word rest ab off n
  end.
Definition node_wordspell_ref (cs : acs) (a : expr) (off : Z) (n : Z) (V : expr) : option acs :=
  let k := kn cs in
  let '(ab, ao) := split_lit (eaddz a off) in
  let m := Z.to_nat n in
  match find_word k ab ao m with
  | Some w =>
      if (lin_ge0 k [(w, 0)] [(V, 0)] && lin_ge0 k [(V, 0)] [(w, 0)])%bool
      then Some (set_kn cs (KWord (SA ab ao) m V :: k)) else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_wordspell (cs : acs) (a : expr) (off : Z) (n : Z) (V : expr) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  let '(ab, ao) := split_lit (eaddz a off) in
  let m := Z.to_nat n in
  match find_word k ab ao m with
  | Some w =>
      if (lin_ge0B bc [(w, 0)] [(V, 0)] && lin_ge0B bc [(V, 0)] [(w, 0)])%bool
      then Some (set_kn cs (KWord (SA ab ao) m V :: k)) else None
  | None => None
  end.

Lemma node_wordspell_eq : forall cs a off n V, node_wordspell cs a off n V = node_wordspell_ref cs a off n V.
Proof.
  intros. unfold node_wordspell, node_wordspell_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition node_bytespell_alt_ref (cs : acs) (a : expr) (off : Z) (V : expr) (a2 : expr) : option acs :=
  let k := kn cs in
  let '(ab, ao) := split_lit (eaddz a off) in
  let '(ab2, ao2) := split_lit (eaddz a2 off) in
  match find_byte2 k ab2 ao2 with
  | Some w =>
      let w' := extK k w in
      if (flat_x k ab ao (ELit 1) && flat_x k ab2 ao2 (ELit 1)
          && lin_ge0 k [(ab, ao)] [(ab2, ao2)] && lin_ge0 k [(ab2, ao2)] [(ab, ao)]
          && lin_ge0 k [(w', 0)] [(V, 0)] && lin_ge0 k [(V, 0)] [(w', 0)])%bool
      then Some (set_kn cs (KWord (SA ab ao) 1 V :: k)) else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_bytespell_alt (cs : acs) (a : expr) (off : Z) (V : expr) (a2 : expr) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  let '(ab, ao) := split_lit (eaddz a off) in
  let '(ab2, ao2) := split_lit (eaddz a2 off) in
  match find_byte2 k ab2 ao2 with
  | Some w =>
      let w' := extKB bc w in
      if (flat_xB bc ab ao (ELit 1) && flat_xB bc ab2 ao2 (ELit 1)
          && lin_ge0B bc [(ab, ao)] [(ab2, ao2)] && lin_ge0B bc [(ab2, ao2)] [(ab, ao)]
          && lin_ge0B bc [(w', 0)] [(V, 0)] && lin_ge0B bc [(V, 0)] [(w', 0)])%bool
      then Some (set_kn cs (KWord (SA ab ao) 1 V :: k)) else None
  | None => None
  end.

Lemma node_bytespell_alt_eq : forall cs a off V a2, node_bytespell_alt cs a off V a2 = node_bytespell_alt_ref cs a off V a2.
Proof.
  intros. unfold node_bytespell_alt, node_bytespell_alt_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition node_summeet_ref (cs : acs) (e1 ea eb : expr) : option acs :=
  let k := kn cs in
  match xlo k e1, xhi k e1, xlo k ea, xhi k ea, xlo k eb, xhi k eb with
  | Some lo1, Some hi1, Some loa, Some hia, Some lob, Some hib =>
      if (lin_ge0 k [(e1, 0)] [(ea, 0); (eb, 0)] && lin_ge0 k [(ea, 0); (eb, 0)] [(e1, 0)])%bool
      then Some (set_kn cs (KRange e1 (Z.max lo1 (loa + lob)) (Z.min hi1 (hia + hib)) :: k)) else None
  | _, _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition node_summeet (cs : acs) (e1 ea eb : expr) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  match xloB bc e1, xhiB bc e1, xloB bc ea, xhiB bc ea, xloB bc eb, xhiB bc eb with
  | Some lo1, Some hi1, Some loa, Some hia, Some lob, Some hib =>
      if (lin_ge0B bc [(e1, 0)] [(ea, 0); (eb, 0)] && lin_ge0B bc [(ea, 0); (eb, 0)] [(e1, 0)])%bool
      then Some (set_kn cs (KRange e1 (Z.max lo1 (loa + lob)) (Z.min hi1 (hia + hib)) :: k)) else None
  | _, _, _, _, _, _ => None
  end.

Lemma node_summeet_eq : forall cs e1 ea eb, node_summeet cs e1 ea eb = node_summeet_ref cs e1 ea eb.
Proof.
  intros. unfold node_summeet, node_summeet_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition andrange1 (k : list kentry) (x : expr) : list kentry :=
  match xlo k x, xhi k x with
  | Some lo, Some hi => if (Z.leb 0 lo && Z.ltb hi two64 && Z.eqb (lo / 8) (hi / 8))%bool
                        then [KRange (mkAnd k x (ELit 7)) (lo mod 8) (hi mod 8)] else []
  | _, _ => []
  end.
Definition node_andrange (cs : acs) : option acs :=
  let k := kn cs in
  Some (set_kn cs (andrange1 k (esub (reg cs 20) (reg cs 10)) ++ andrange1 k (esub (reg cs 19) (reg cs 11)) ++ k)).

Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id, args with
  | 27%nat, _ => node_shdisj_maps cs
  | 28%nat, [e1; e2] => node_linkrange cs e1 e2
  | 29%nat, [ELit a; ELit m] => node_splitzero cs a m
  | 30%nat, [x; y; z; ELit m] => node_disjdom cs x y z m
  | 31%nat, [b; Lnew] => node_zeroprefix cs b Lnew
  | 32%nat, [x; ELit a; ELit s] => node_srlstep cs x a s
  | 33%nat, [e; ELit s] => node_srlrange cs e s
  | 34%nat, [a; ELit off; v] => node_bytespell cs a off v
  | 35%nat, _ => node_andrange cs
  | 36%nat, [a; ELit off; ELit n; v] => node_wordspell cs a off n v
  | 37%nat, [a; ELit off; v; a2] => node_bytespell_alt cs a off v a2
  | 38%nat, [e1; ea; eb] => node_summeet cs e1 ea eb
  | _, _ => None
  end.
End WithSegs.
End YN.
