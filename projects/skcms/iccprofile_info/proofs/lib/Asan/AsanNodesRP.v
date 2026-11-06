(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Module RPN.

(* [comment removed for export] *)
Record rptab : Type := RPT {
  rp_entry : Z;               (* [comment removed for export] *)
  rc_entry : Z; rc_exit : Z;  (* [comment removed for export] *)
  qs_entry : Z; qs_exit : Z;  (* [comment removed for export] *)
  qd_entry : Z; qd_exit : Z;  (* [comment removed for export] *)
  rp_gsb : Z; rp_csb : Z;     (* [comment removed for export] *)
  rp_gm1 : Z; rp_cm1 : Z;     (* [comment removed for export] *)
  rp_gm2 : Z; rp_cm2 : Z;     (* [comment removed for export] *)
  rp_ghi : Z; rp_chi : Z      (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition RP_ASAN : rptab := RPT 0x53bb0 0x436e4 0x4373c 0x51a74 0x51aac 0x51abc 0x51af4 0x9eaf0 0xa6bb8 0x9eaf8 0xa78a8 0x9eb00 0xa78b0 0x9eb08 0xa78a0.
(* [comment removed for export] *)
Definition RP_BOTH : rptab := RPT 0x53bdc 0x43710 0x43768 0x51aa0 0x51ad8 0x51ae8 0x51b20 0x9f920 0xa79b8 0x9f928 0xa86a8 0x9f930 0xa86b0 0x9f938 0xa86a0.   (* [comment removed for export] *)

Definition SB : Z := 0x7fff8000.
Definition kLowEnd : Z := 0x7fff7fff.
Definition kHighBeg : Z := 0x10007fff8000.
Definition kHighEnd : Z := 0x7fffffffffff.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.
Variable T : rptab.

(* [comment removed for export] *)
Definition lit_cell (k : list kentry) (cell v : Z) : bool :=
  flat_x k (ELit 0) cell (ELit 8) &&
  match know_lookup segs k (ELit 0) cell 8 false [] [] with
  | LHit e sc _ => match sc, erange k e with [], Some (lo, hi) => Z.eqb lo v && Z.eqb hi v | _, _ => false end
  | _ => false
  end.
Definition lit_cellB (bc : bctx) (k : list kentry) (cell v : Z) : bool :=
  flat_xB bc (ELit 0) cell (ELit 8) &&
  match know_lookupB segs bc (ELit 0) cell 8 false [] [] with
  | LHit e sc _ => match sc, erangeB bc e with [], Some (lo, hi) => Z.eqb lo v && Z.eqb hi v | _, _ => false end
  | _ => false
  end.
Lemma lit_cellB_eqf : forall k, lit_cellB (mkbc k) k = lit_cell k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold lit_cellB, lit_cell.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition img8 (k : list kentry) (a : Z) : bool := img_cov k a (a + 8).

Definition img8B (bc : bctx) (k : list kentry) (a : Z) : bool := img_covB bc a (a + 8).

Lemma img8B_eqf : forall k, img8B (mkbc k) k = img8 k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold img8B, img8.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition qc_word (k : list kentry) (x : expr) : expr * Z :=
  split_lit (mkAnd k (eadd (ELit SB) (mkSrl k x 3)) (ELit (two64 - 8))).
Definition qc_wordB (bc : bctx) (k : list kentry) (x : expr) : expr * Z :=
  split_lit (mkAndB bc (eadd (ELit SB) (mkSrlB bc x 3)) (ELit (two64 - 8))).
Lemma qc_wordB_eqf : forall k, qc_wordB (mkbc k) k = qc_word k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold qc_wordB, qc_word.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition qc_shadow_ok (k : list kentry) (shb she e1 : expr) (kmax : Z) (zok : bool) : bool :=
  let '(lb, lk) := split_lit shb in
  let '(hb, hk) := split_lit she in
  let Lfull := esub she shb in
  (lin_ge0 k [(she, 0)] [(shb, 0)] && flat_x k lb lk (eaddz Lfull 1)
   && (kzero_x k k lb lk (eaddz Lfull 1)
       || (kzero_x k k lb lk Lfull && flat_x k hb hk (ELit 1)
           && match know_lookup segs k hb hk 1 false [] [] with
              | LHit v0 [] _ =>
                  let v := extK k v0 in
                  match erange k v with
                  | Some (lo, hi) => Z.leb 0 lo && Z.leb hi kmax && ((zok && Z.eqb hi 0) || lin_ge0 k [(v, 0)] [(mkAnd k e1 (ELit 7), 1)])
                  | None => false
                  end
              | _ => false
              end)))%bool.
Definition qc_shadow_okB (bc : bctx) (k : list kentry) (shb she e1 : expr) (kmax : Z) (zok : bool) : bool :=
  let '(lb, lk) := split_lit shb in
  let '(hb, hk) := split_lit she in
  let Lfull := esub she shb in
  (lin_ge0B bc [(she, 0)] [(shb, 0)] && flat_xB bc lb lk (eaddz Lfull 1)
   && (kzero_xB bc k lb lk (eaddz Lfull 1)
       || (kzero_xB bc k lb lk Lfull && flat_xB bc hb hk (ELit 1)
           && match know_lookupB segs bc hb hk 1 false [] [] with
              | LHit v0 [] _ =>
                  let v := extKB bc v0 in
                  match erangeB bc v with
                  | Some (lo, hi) => Z.leb 0 lo && Z.leb hi kmax && ((zok && Z.eqb hi 0) || lin_ge0B bc [(v, 0)] [(mkAndB bc e1 (ELit 7), 1)])
                  | None => false
                  end
              | _ => false
              end)))%bool.
Lemma qc_shadow_okB_eqf : forall k, qc_shadow_okB (mkbc k) k = qc_shadow_ok k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold qc_shadow_okB, qc_shadow_ok.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition readable_lit_entry (K : kentry) : option (expr * Z * Z) :=
  match K with
  | KZero (SA b o) (ELit l) | KFill (SA b o) (ELit l) _ | KUnk (SA b o) (ELit l) | KWr (SA b o) (ELit l) => Some (b, o, l)
  | _ => None
  end.
(* [comment removed for export] *)
Definition covers_lit (k : list kentry) (zb : expr) (lo hi : Z) : bool :=
  existsb (fun K => match readable_lit_entry K with
                    | Some (b, o, l) => expr_eqb b zb && Z.leb o lo && Z.leb hi (o + l mod two64)
                    | None => false
                    end) k.
(* [comment removed for export] *)
Definition hull_lo (k : list kentry) (zb : expr) (o : Z) : Z := if Z.leb 3 (ealign k zb) then o - o mod 8 else o - 7.
Definition hull_loB (bc : bctx) (k : list kentry) (zb : expr) (o : Z) : Z := if Z.leb 3 (ealignB bc zb) then o - o mod 8 else o - 7.
Lemma hull_loB_eqf : forall k, hull_loB (mkbc k) k = hull_lo k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold hull_loB, hull_lo.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf. reflexivity.
Qed.
Definition qc_cover1 (k : list kentry) (beg en : expr) (words : bool) (zb : expr) (zk zl : Z) : bool :=
  match xlo k zb, xhi k zb with
  | Some zblo, Some zbhi =>
      (Z.ltb 0 zl && Z.leb 0 zblo && Z.leb SB (zblo + zk) && Z.ltb (8 * zbhi) two64 && Z.ltb (8 * (zbhi + zk + zl + 8)) two64
       && lin_ge0 k [(beg, 0)] [(EMd M_MUL (ELit 8) zb, 8 * (zk - SB))]
       && lin_ge0 k [(EMd M_MUL (ELit 8) zb, 8 * (zk - SB) + 8 * zl)] [(en, 0)]
       && (negb words || covers_lit k zb (hull_lo k zb zk) (zk + zl + 7)))%bool
  | _, _ => false
  end.
Definition qc_cover1B (bc : bctx) (k : list kentry) (beg en : expr) (words : bool) (zb : expr) (zk zl : Z) : bool :=
  match xloB bc zb, xhiB bc zb with
  | Some zblo, Some zbhi =>
      (Z.ltb 0 zl && Z.leb 0 zblo && Z.leb SB (zblo + zk) && Z.ltb (8 * zbhi) two64 && Z.ltb (8 * (zbhi + zk + zl + 8)) two64
       && lin_ge0B bc [(beg, 0)] [(EMd M_MUL (ELit 8) zb, 8 * (zk - SB))]
       && lin_ge0B bc [(EMd M_MUL (ELit 8) zb, 8 * (zk - SB) + 8 * zl)] [(en, 0)]
       && (negb words || covers_lit k zb (hull_loB bc k zb zk) (zk + zl + 7)))%bool
  | _, _ => false
  end.
Lemma qc_cover1B_eqf : forall k, qc_cover1B (mkbc k) k = qc_cover1 k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold qc_cover1B, qc_cover1.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf. reflexivity.
Qed.
Definition qc_cover (k : list kentry) (beg en : expr) (words : bool) : bool :=
  existsb (fun K => match K with KZero (SA zb zk) (ELit zl) => qc_cover1 k beg en words zb zk zl | _ => false end) k.
Definition qc_coverB (bc : bctx) (k : list kentry) (beg en : expr) (words : bool) : bool :=
  existsb (fun K => match K with KZero (SA zb zk) (ELit zl) => qc_cover1B bc k beg en words zb zk zl | _ => false end) k.
Lemma qc_coverB_eqf : forall k, qc_coverB (mkbc k) k = qc_cover k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold qc_coverB, qc_cover.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf, ?qc_cover1B_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition and7_of (k : list kentry) (m ne : expr) : bool :=
  expr_eqb m (mkAnd k ne (ELit 7))
  || match m with
     | EAlu ALU_AND ne' (ELit 7) => lin_ge0 k [(ne', 0)] [(ne, 0)] && lin_ge0 k [(ne, 0)] [(ne', 0)]
     | _ => false
     end.
Definition and7_ofB (bc : bctx) (k : list kentry) (m ne : expr) : bool :=
  expr_eqb m (mkAndB bc ne (ELit 7))
  || match m with
     | EAlu ALU_AND ne' (ELit 7) => lin_ge0B bc [(ne', 0)] [(ne, 0)] && lin_ge0B bc [(ne, 0)] [(ne', 0)]
     | _ => false
     end.
Lemma and7_ofB_eqf : forall k, and7_ofB (mkbc k) k = and7_of k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold and7_ofB, and7_of.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf, ?qc_cover1B_eqf, ?qc_coverB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition vshape0 (k : list kentry) (v ne : expr) : bool :=
  match v with
  | EAlu ALU_ADD m1 (EMd M_MUL (ELit 250) (EAlu ALU_SLTU m2 (ELit 1))) => expr_eqb m1 m2 && and7_of k m1 ne
  | _ => false
  end.
Definition vshape0B (bc : bctx) (k : list kentry) (v ne : expr) : bool :=
  match v with
  | EAlu ALU_ADD m1 (EMd M_MUL (ELit 250) (EAlu ALU_SLTU m2 (ELit 1))) => expr_eqb m1 m2 && and7_ofB bc k m1 ne
  | _ => false
  end.
Lemma vshape0B_eqf : forall k, vshape0B (mkbc k) k = vshape0 k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold vshape0B, vshape0.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf, ?qc_cover1B_eqf, ?qc_coverB_eqf, ?and7_ofB_eqf. reflexivity.
Qed.
Definition vshape (k : list kentry) (v ne : expr) : bool :=
  vshape0 k v ne || match v with EExt false 0%nat 1%nat v' => vshape0 k v' ne | _ => false end.

Definition vshapeB (bc : bctx) (k : list kentry) (v ne : expr) : bool :=
  vshape0B bc k v ne || match v with EExt false 0%nat 1%nat v' => vshape0B bc k v' ne | _ => false end.

Lemma vshapeB_eqf : forall k, vshapeB (mkbc k) k = vshape k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold vshapeB, vshape.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf, ?qc_cover1B_eqf, ?qc_coverB_eqf, ?and7_ofB_eqf, ?vshape0B_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition sh_alloc (k : list kentry) (beg en : expr) (words : bool) (kmax : Z) : bool :=
  let nE := esub en beg in
  let shb := eadd (ELit SB) (mkSrl k beg 3) in
  let '(lb, lk) := split_lit shb in
  let zl := mkSrl k nE 3 in
  (* [comment removed for export] *)
  let zl0 := match xlo k zl, xhi k zl with Some a, Some b => if Z.eqb a b then ELit a else zl | _, _ => zl end in
  let '(hb, hk) := split_lit (eadd shb zl0) in
  match xhi k nE with
  | Some nhi =>
    (Z.leb 3 (ealign k beg) && lin_ge0 k [(en, 0)] [(beg, 1)]
     && flat_x k lb lk (eaddz zl 2) && match zl0 with ELit 0 => true | _ => kzero_x k k lb lk zl0 end
     && (negb words || covers_lit k lb (hull_lo k lb lk) (lk + nhi / 8 + 8))
     && match erange k (mkAnd k nE (ELit 7)) with
        | Some (rlo, rhi) =>
            Z.eqb rhi 0
            || (Z.leb 1 rlo && flat_x k hb hk (ELit 1)
                && match know_lookup segs k hb hk 1 false [] [] with
                   | LHit v0 [] _ =>
                       let v := extK k v0 in
                       (vshape k v nE && Z.leb 7 kmax)                                  (* [comment removed for export] *)
                       || match erange k v with
                          | Some (lo, hi) => Z.leb 0 lo && Z.leb hi kmax && lin_ge0 k [(v, 0)] [(mkAnd k nE (ELit 7), 0)]
                          | None => false
                          end
                   | _ => false
                   end)
            || (flat_x k hb hk (ELit 1) && Z.leb 7 kmax                                (* [comment removed for export] *)
                && match know_lookup segs k hb hk 1 false [] [] with
                   | LHit v0 [] _ => vshape k (extK k v0) nE
                   | _ => false
                   end)
        | None => false
        end)%bool
  | None => false
  end.

Definition sh_allocB (bc : bctx) (k : list kentry) (beg en : expr) (words : bool) (kmax : Z) : bool :=
  let nE := esub en beg in
  let shb := eadd (ELit SB) (mkSrlB bc beg 3) in
  let '(lb, lk) := split_lit shb in
  let zl := mkSrlB bc nE 3 in
  (* [comment removed for export] *)
  let zl0 := match xloB bc zl, xhiB bc zl with Some a, Some b => if Z.eqb a b then ELit a else zl | _, _ => zl end in
  let '(hb, hk) := split_lit (eadd shb zl0) in
  match xhiB bc nE with
  | Some nhi =>
    (Z.leb 3 (ealignB bc beg) && lin_ge0B bc [(en, 0)] [(beg, 1)]
     && flat_xB bc lb lk (eaddz zl 2) && match zl0 with ELit 0 => true | _ => kzero_xB bc k lb lk zl0 end
     && (negb words || covers_lit k lb (hull_loB bc k lb lk) (lk + nhi / 8 + 8))
     && match erangeB bc (mkAndB bc nE (ELit 7)) with
        | Some (rlo, rhi) =>
            Z.eqb rhi 0
            || (Z.leb 1 rlo && flat_xB bc hb hk (ELit 1)
                && match know_lookupB segs bc hb hk 1 false [] [] with
                   | LHit v0 [] _ =>
                       let v := extKB bc v0 in
                       (vshapeB bc k v nE && Z.leb 7 kmax)                                  (* [comment removed for export] *)
                       || match erangeB bc v with
                          | Some (lo, hi) => Z.leb 0 lo && Z.leb hi kmax && lin_ge0B bc [(v, 0)] [(mkAndB bc nE (ELit 7), 0)]
                          | None => false
                          end
                   | _ => false
                   end)
            || (flat_xB bc hb hk (ELit 1) && Z.leb 7 kmax                                (* [comment removed for export] *)
                && match know_lookupB segs bc hb hk 1 false [] [] with
                   | LHit v0 [] _ => vshapeB bc k (extKB bc v0) nE
                   | _ => false
                   end)
        | None => false
        end)%bool
  | None => false
  end.

Lemma sh_allocB_eqf : forall k, sh_allocB (mkbc k) k = sh_alloc k.
Proof.
  intros k. repeat (apply functional_extensionality; intros ?). unfold sh_allocB, sh_alloc.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf, ?qc_cover1B_eqf, ?qc_coverB_eqf, ?and7_ofB_eqf, ?vshape0B_eqf, ?vshapeB_eqf. reflexivity.
Qed.
Definition node_rpoison_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    (* [comment removed for export] *)
    let en := eadd beg ne in
    let e1 := eaddz en (-1) in
    let shb := eadd (ELit SB) (mkSrl k beg 3) in
    let she := eadd (ELit SB) (mkSrl k e1 3) in
    match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      if (Z.leb 16 nlo && Z.leb nhi (2 ^ 40)
          && ((Z.leb (bhi + nhi) kLowEnd || lin_ge0 k [(ELit kLowEnd, 0)] [(beg, 0); (ne, 0)]) || (Z.leb kHighBeg blo && (Z.leb (bhi + nhi) kHighEnd || lin_ge0 k [(ELit kHighEnd, 0)] [(beg, 0); (ne, 0)])))
          && (if qc_shadow_ok k shb she e1 7 false then true else if sh_alloc k beg en false 7 then true else qc_cover k beg en false)
          && Z.leb 80 splo && Z.ltb sphi two64
          && Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72)
          && Z.leb (rp_chi T + 8) (splo - 72) && Z.leb (rp_cm2 T + 8) (splo - 72) && Z.leb (rp_cm1 T + 8) (splo - 72)
          && Z.leb (rp_csb T + 8) (splo - 72) && Z.leb (rp_ghi T + 8) (splo - 72) && Z.leb (rp_gm2 T + 8) (splo - 72)
          && Z.leb (rp_gm1 T + 8) (splo - 72) && Z.leb (rp_gsb T + 8) (splo - 72)
          && Z.leb 0 (rp_gsb T) && Z.leb 0 (rp_gm1 T) && Z.leb 0 (rp_gm2 T) && Z.leb 0 (rp_ghi T)
          && Z.leb 0 (rp_csb T) && Z.leb 0 (rp_cm1 T) && Z.leb 0 (rp_cm2 T) && Z.leb 0 (rp_chi T)
          && kwritable k k qb qk 72 && flat_x k qb qk (ELit 72)
          && img8 k (rp_gsb T) && img8 k (rp_gm1 T) && img8 k (rp_gm2 T) && img8 k (rp_ghi T)
          && img8 k (rp_cm1 T) && img8 k (rp_cm2 T)
          && lit_cell k (rp_csb T) SB && lit_cell k (rp_chi T) kHighEnd)%bool
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _ => None
    end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_rpoison (cs : acs) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    (* [comment removed for export] *)
    let en := eadd beg ne in
    let e1 := eaddz en (-1) in
    let shb := eadd (ELit SB) (mkSrlB bc beg 3) in
    let she := eadd (ELit SB) (mkSrlB bc e1 3) in
    match xloB bc ne, xhiB bc ne, xloB bc beg, xhiB bc beg, xloB bc sp, xhiB bc sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      if (Z.leb 16 nlo && Z.leb nhi (2 ^ 40)
          && ((Z.leb (bhi + nhi) kLowEnd || lin_ge0B bc [(ELit kLowEnd, 0)] [(beg, 0); (ne, 0)]) || (Z.leb kHighBeg blo && (Z.leb (bhi + nhi) kHighEnd || lin_ge0B bc [(ELit kHighEnd, 0)] [(beg, 0); (ne, 0)])))
          && (if qc_shadow_okB bc k shb she e1 7 false then true else if sh_allocB bc k beg en false 7 then true else qc_coverB bc k beg en false)
          && Z.leb 80 splo && Z.ltb sphi two64
          && Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72)
          && Z.leb (rp_chi T + 8) (splo - 72) && Z.leb (rp_cm2 T + 8) (splo - 72) && Z.leb (rp_cm1 T + 8) (splo - 72)
          && Z.leb (rp_csb T + 8) (splo - 72) && Z.leb (rp_ghi T + 8) (splo - 72) && Z.leb (rp_gm2 T + 8) (splo - 72)
          && Z.leb (rp_gm1 T + 8) (splo - 72) && Z.leb (rp_gsb T + 8) (splo - 72)
          && Z.leb 0 (rp_gsb T) && Z.leb 0 (rp_gm1 T) && Z.leb 0 (rp_gm2 T) && Z.leb 0 (rp_ghi T)
          && Z.leb 0 (rp_csb T) && Z.leb 0 (rp_cm1 T) && Z.leb 0 (rp_cm2 T) && Z.leb 0 (rp_chi T)
          && kwritableB bc k qb qk 72 && flat_xB bc qb qk (ELit 72)
          && img8B bc k (rp_gsb T) && img8B bc k (rp_gm1 T) && img8B bc k (rp_gm2 T) && img8B bc k (rp_ghi T)
          && img8B bc k (rp_cm1 T) && img8B bc k (rp_cm2 T)
          && lit_cellB bc k (rp_csb T) SB && lit_cellB bc k (rp_chi T) kHighEnd)%bool
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _ => None
    end
  | None => None
  end.

Lemma node_rpoison_eq : forall cs, node_rpoison cs = node_rpoison_ref cs.
Proof.
  intros. unfold node_rpoison, node_rpoison_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf, ?qc_cover1B_eqf, ?qc_coverB_eqf, ?and7_ofB_eqf, ?vshape0B_eqf, ?vshapeB_eqf, ?sh_allocB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition rc_regs (sr : list expr) (e1 e2 e3 e20 : expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 11 e1) 12 e2) 13 e3) 14 (ELit 0)) 15 (ELit 0)) 20 e20.
Definition node_readcheck_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rc_entry T)) then None else
  let dst := reg cs 9 in let re := reg cs 10 in
  let '(bb, bk) := split_lit dst in
  let m := (SB + bk / 8) mod 8 in
  let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8 - m)) (mkSrl k bb 3)) in
  match xlo k re, xhi k re, xhi k dst with
  | Some rlo, Some rhi, Some dhi =>
    if (Z.leb 1 rlo && Z.leb rhi 64 && Z.ltb (dhi + 64) two64 && Z.leb 6 (ealign k bb) && flat_x k bb bk (ELit 1)
        && fresh_ok nx0 cs
        && flat_x k hb hk (ELit 16) && kzero_x k k hb hk (ELit 16)
        && Z.leb 0 (rp_gsb T) && Z.leb 0 (rp_csb T) && img8 k (rp_gsb T) && lit_cell k (rp_csb T) SB)%bool
    then
      let e1 := eadd (ELit (SB + bk / 8)) (mkSrl k bb 3) in
      let e3 := eaddz (eadd dst re) (-1) in
      let e2 := eadd (ELit SB) (mkSrl k e3 3) in
      let e20 := eaddz (eaddz (reg cs 8) (-2048)) (-72) in
      Some (with_ss cs (mk_ss (rc_exit T) (rc_regs (s_regs (a_ss cs)) e1 e2 e3 e20) k (nxt cs)))
    else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition node_readcheck (cs : acs) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  if negb (Z.eqb (pc cs) (rc_entry T)) then None else
  let dst := reg cs 9 in let re := reg cs 10 in
  let '(bb, bk) := split_lit dst in
  let m := (SB + bk / 8) mod 8 in
  let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8 - m)) (mkSrlB bc bb 3)) in
  match xloB bc re, xhiB bc re, xhiB bc dst with
  | Some rlo, Some rhi, Some dhi =>
    if (Z.leb 1 rlo && Z.leb rhi 64 && Z.ltb (dhi + 64) two64 && Z.leb 6 (ealignB bc bb) && flat_xB bc bb bk (ELit 1)
        && fresh_ok nx0 cs
        && flat_xB bc hb hk (ELit 16) && kzero_xB bc k hb hk (ELit 16)
        && Z.leb 0 (rp_gsb T) && Z.leb 0 (rp_csb T) && img8B bc k (rp_gsb T) && lit_cellB bc k (rp_csb T) SB)%bool
    then
      let e1 := eadd (ELit (SB + bk / 8)) (mkSrlB bc bb 3) in
      let e3 := eaddz (eadd dst re) (-1) in
      let e2 := eadd (ELit SB) (mkSrlB bc e3 3) in
      let e20 := eaddz (eaddz (reg cs 8) (-2048)) (-72) in
      Some (with_ss cs (mk_ss (rc_exit T) (rc_regs (s_regs (a_ss cs)) e1 e2 e3 e20) k (nxt cs)))
    else None
  | _, _, _ => None
  end.

Lemma node_readcheck_eq : forall cs, node_readcheck cs = node_readcheck_ref cs.
Proof.
  intros. unfold node_readcheck, node_readcheck_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf, ?qc_cover1B_eqf, ?qc_coverB_eqf, ?and7_ofB_eqf, ?vshape0B_eqf, ?vshapeB_eqf, ?sh_allocB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Definition node_quick_ref (src : bool) (cs : acs) : option acs :=
  let k := kn cs in
  let entry := if src then qs_entry T else qd_entry T in
  let exitpc := if src then qs_exit T else qd_exit T in
  let rb := if src then 11%nat else 10%nat in
  let re := if src then 19%nat else 20%nat in
  if negb (Z.eqb (pc cs) entry) then None else
  let beg := reg cs rb in let en := reg cs re in
  let e1 := eaddz en (-1) in
  let shb := eadd (ELit SB) (mkSrl k beg 3) in
  let she := eadd (ELit SB) (mkSrl k e1 3) in
  let '(w1b, w1k) := qc_word k beg in
  let '(w2b, w2k) := qc_word k e1 in
  match xlo k beg, xhi k beg, xlo k en, xhi k en with
  | Some blo, Some bhi, Some elo, Some ehi =>
    if (Z.leb 1 blo && Z.ltb bhi (2 ^ 47) && Z.leb 2 elo && Z.leb ehi (2 ^ 47)
        && lin_ge0 k [(e1, 0)] [(beg, 0)]
        && (if (flat_x k w1b w1k (ELit 8) && kn_readable segs k k w1b w1k 8
                && flat_x k w2b w2k (ELit 8) && kn_readable segs k k w2b w2k 8
                && qc_shadow_ok k shb she e1 127 true) then true
            else if sh_alloc k beg en true 127 then true else qc_cover k beg en true)
        && Z.leb 0 (rp_gsb T) && Z.leb 0 (rp_csb T) && img8 k (rp_gsb T) && lit_cell k (rp_csb T) SB
        && fresh_ok nx0 cs)%bool
    then
      let v := nxt cs in
      let sr := s_regs (a_ss cs) in
      let sr' := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr re e1) 13 (EVar v)) 14 (EVar (S v))) 15 (EVar (S (S v))))
                        16 (EVar (S (S (S v))))) 17 (EVar (S (S (S (S v))))) in
      Some (with_ss cs (mk_ss exitpc sr' k (v + 5)))
    else None
  | _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition node_quick (src : bool) (cs : acs) : option acs :=
  let k := kn cs in
  let bc := mkbc k in
  let entry := if src then qs_entry T else qd_entry T in
  let exitpc := if src then qs_exit T else qd_exit T in
  let rb := if src then 11%nat else 10%nat in
  let re := if src then 19%nat else 20%nat in
  if negb (Z.eqb (pc cs) entry) then None else
  let beg := reg cs rb in let en := reg cs re in
  let e1 := eaddz en (-1) in
  let shb := eadd (ELit SB) (mkSrlB bc beg 3) in
  let she := eadd (ELit SB) (mkSrlB bc e1 3) in
  let '(w1b, w1k) := qc_wordB bc k beg in
  let '(w2b, w2k) := qc_wordB bc k e1 in
  match xloB bc beg, xhiB bc beg, xloB bc en, xhiB bc en with
  | Some blo, Some bhi, Some elo, Some ehi =>
    if (Z.leb 1 blo && Z.ltb bhi (2 ^ 47) && Z.leb 2 elo && Z.leb ehi (2 ^ 47)
        && lin_ge0B bc [(e1, 0)] [(beg, 0)]
        && (if (flat_xB bc w1b w1k (ELit 8) && kn_readableB segs bc k w1b w1k 8
                && flat_xB bc w2b w2k (ELit 8) && kn_readableB segs bc k w2b w2k 8
                && qc_shadow_okB bc k shb she e1 127 true) then true
            else if sh_allocB bc k beg en true 127 then true else qc_coverB bc k beg en true)
        && Z.leb 0 (rp_gsb T) && Z.leb 0 (rp_csb T) && img8B bc k (rp_gsb T) && lit_cellB bc k (rp_csb T) SB
        && fresh_ok nx0 cs)%bool
    then
      let v := nxt cs in
      let sr := s_regs (a_ss cs) in
      let sr' := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr re e1) 13 (EVar v)) 14 (EVar (S v))) 15 (EVar (S (S v))))
                        16 (EVar (S (S (S v))))) 17 (EVar (S (S (S (S v))))) in
      Some (with_ss cs (mk_ss exitpc sr' k (v + 5)))
    else None
  | _, _, _, _ => None
  end.

Lemma node_quick_eq : forall src cs, node_quick src cs = node_quick_ref src cs.
Proof.
  intros. unfold node_quick, node_quick_ref. cbv zeta.
  rewrite ?lin_ge0B_eqf, ?xinsideB_eqf, ?erangeB_eqf, ?xloB_eqf, ?xhiB_eqf, ?base_rangeB_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?ranges_apartB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?mkAndKB_eqf, ?mkOrB_eqf, ?extKB_eqf, ?foldKB_eqf, ?len_eqbB_eqf, ?page_alignedB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xb2B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?off_image_xB_eqf, ?end_hiB_eqf, ?lin_apartB_eqf, ?decide_branchB_eqf, ?mkAluKB_eqf, ?mkAluwKB_eqf, ?mkMdKB_eqf, ?lin_nowrapB_eqf, ?lin_nowrapRB_eqf, ?find_containingB_eqf, ?shadow_ofB_eqf, ?inside_mapsB_eqf, ?safe_rangeB_eqf, ?lin_brangeB_eqf, ?lin_srangeB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?kfill_xB_eqf, ?kn_readableB_eqf, ?kn_overlayB_eqf, ?know_lookupB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?qc_wordB_eqf, ?qc_shadow_okB_eqf, ?hull_loB_eqf, ?qc_cover1B_eqf, ?qc_coverB_eqf, ?and7_ofB_eqf, ?vshape0B_eqf, ?vshapeB_eqf, ?sh_allocB_eqf. reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint first_false (i : nat) (l : list bool) : nat :=
  match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.
Definition diag_rpoison (cs : acs) : nat :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then 100%nat else
  match ret_lit cs with
  | None => 101%nat
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    let en := eadd beg ne in
    let e1 := eaddz en (-1) in
    let shb := eadd (ELit SB) (mkSrl k beg 3) in
    let she := eadd (ELit SB) (mkSrl k e1 3) in
    match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      first_false 1 [Z.leb 16 nlo; Z.leb nhi (2 ^ 40);
        ((Z.leb (bhi + nhi) kLowEnd || lin_ge0 k [(ELit kLowEnd, 0)] [(beg, 0); (ne, 0)]) || (Z.leb kHighBeg blo && (Z.leb (bhi + nhi) kHighEnd || lin_ge0 k [(ELit kHighEnd, 0)] [(beg, 0); (ne, 0)])));
        (qc_shadow_ok k shb she e1 7 false || sh_alloc k beg en false 7 || qc_cover k beg en false); true; Z.leb 80 splo; Z.ltb sphi two64;
        Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72); Z.leb (rp_chi T + 8) (splo - 72);
        kwritable k k qb qk 72; flat_x k qb qk (ELit 72); qc_shadow_ok k shb she e1 7 false; sh_alloc k beg en false 7; qc_cover k beg en false;
        img8 k (rp_gsb T); img8 k (rp_gm1 T); img8 k (rp_gm2 T); img8 k (rp_ghi T); img8 k (rp_cm1 T); img8 k (rp_cm2 T);
        lit_cell k (rp_csb T) SB; lit_cell k (rp_chi T) kHighEnd; fresh_ok nx0 cs]%bool
    | _, _, _, _, _, _ => 102%nat
    end
  end.
Definition diag_readcheck (cs : acs) : nat :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rc_entry T)) then 100%nat else
  let dst := reg cs 9 in let re := reg cs 10 in
  let '(bb, bk) := split_lit dst in
  let m := (SB + bk / 8) mod 8 in
  let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8 - m)) (mkSrl k bb 3)) in
  match xlo k re, xhi k re, xhi k dst with
  | Some rlo, Some rhi, Some dhi =>
      first_false 1 [Z.leb 1 rlo; Z.leb rhi 64; Z.ltb (dhi + 64) two64; Z.leb 6 (ealign k bb); flat_x k bb bk (ELit 1);
        fresh_ok nx0 cs; flat_x k hb hk (ELit 16); kzero_x k k hb hk (ELit 16); img8 k (rp_gsb T); lit_cell k (rp_csb T) SB]%bool
  | _, _, _ => 102%nat
  end.

(* [comment removed for export] *)
Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 100 then node_rpoison cs
  else if Nat.eqb id 101 then node_readcheck cs
  else if Nat.eqb id 102 then node_quick true cs
  else if Nat.eqb id 103 then node_quick false cs
  else None.
End WithSegs.
End RPN.
