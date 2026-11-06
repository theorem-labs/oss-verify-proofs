(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module RPN.

(* [comment removed for export] *)
Record rptab : Type := RPT {
  rp_entry : Z;               (* [comment removed for export] *)
  rc_entry : Z; rc_exit : Z;  (* [comment removed for export] *)
  rp_gsb : Z; rp_csb : Z;     (* [comment removed for export] *)
  rp_gm1 : Z; rp_cm1 : Z;     (* [comment removed for export] *)
  rp_gm2 : Z; rp_cm2 : Z;     (* [comment removed for export] *)
  rp_ghi : Z; rp_chi : Z;     (* [comment removed for export] *)
  rp_gfl : Z; rp_cfl : Z;     (* [comment removed for export] *)
  rp_ccp : Z;                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  rp_pg : Z; rp_pgx : Z;      (* [comment removed for export] *)
  rp_isrc : Z; rp_isrcx : Z;  (* [comment removed for export] *)
  rp_idst : Z; rp_idstx : Z;  (* [comment removed for export] *)
  rp_clz : Z; rp_clzx : Z;    (* [comment removed for export] *)
  rp_bsl : Z; rp_bslx : Z;    (* [comment removed for export] *)
  rp_ic : Z; rp_icx : Z       (* [comment removed for export] *)
}.
Definition RP_ASAN : rptab := RPT 0x569ac 0x45fb0 0x46008 0xaae80 0xb35f8 0xaae88 0xb42e8 0xaae90 0xb42f0 0xaae98 0xb42e0 0xaae78 0xb0df8 0xb2e5c
  0x33e2c 0x33ec0 0x54870 0x548a8 0x548b8 0x548f0 0x38298 0x38340 0x3838c 0x383a4
  0x385b4 0x38650.   (* [comment removed for export] *)
Definition RP_BOTH : rptab := RPT 0x5699c 0x45fa0 0x45ff8 0xa94b8 0xb1bb8 0xa94c0 0xb28a8 0xa94c8 0xb28b0 0xa94d0 0xb28a0 0xa94b0 0xaf3b8 0xb141c
  0x33e1c 0x33eb0 0x54860 0x54898 0x548a8 0x548e0 0x38288 0x38330 0x3837c 0x38394
  0x385a4 0x38640.   (* [comment removed for export] *)

Definition SB : Z := 0x7fff8000.
Definition kLowEnd : Z := 0x7fff7fff.
Definition kHighBeg : Z := 0x10007fff8000.
Definition kHighEnd : Z := 0x7fffffffffff.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : N.
Variable T : rptab.

(* [comment removed for export] *)
Definition lit_cell (k : list kentry) (cell v : Z) : bool :=
  flat_x k (ELit 0) cell (ELit 8) &&
  match know_lookup segs k (ELit 0) cell 8 false [] [] with
  | LHit e sc _ => match sc, erange k e with [], Some (lo, hi) => Z.eqb lo v && Z.eqb hi v | _, _ => false end
  | _ => false
  end.
(* [comment removed for export] *)
Definition img8 (k : list kentry) (a : Z) : bool := img_cov k a (a + 8).

Definition node_rpoison_int_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    (* [comment removed for export] *)
    let '(bb, bk) := split_lit beg in
    let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8)) (mkSrl k bb 3)) in
    match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      let L := (bk + nhi - 1) / 8 - bk / 8 + 1 in
      if (Z.leb 16 nlo && Z.leb nhi (2 ^ 40)
          && (Z.leb (bhi + nhi) kLowEnd || (Z.leb kHighBeg blo && Z.leb (bhi + nhi) kHighEnd)
              || off_band k (a_maps cs) bb bk ne)   (* [comment removed for export] *)
          && Z.leb 3 (ealign k bb) && flat_x k bb bk (ELit 1)
          && Z.leb 80 splo && Z.ltb sphi two64
          && Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72)
          && Z.leb (rp_chi T + 8) (splo - 72) && Z.leb (rp_cm2 T + 8) (splo - 72) && Z.leb (rp_cm1 T + 8) (splo - 72)
          && Z.leb (rp_csb T + 8) (splo - 72) && Z.leb (rp_ghi T + 8) (splo - 72) && Z.leb (rp_gm2 T + 8) (splo - 72)
          && Z.leb (rp_gm1 T + 8) (splo - 72) && Z.leb (rp_gsb T + 8) (splo - 72)
          && Z.leb 0 (rp_gsb T) && Z.leb 0 (rp_gm1 T) && Z.leb 0 (rp_gm2 T) && Z.leb 0 (rp_ghi T)
          && Z.leb 0 (rp_csb T) && Z.leb 0 (rp_cm1 T) && Z.leb 0 (rp_cm2 T) && Z.leb 0 (rp_chi T)
          && kwritable k k qb qk 72 && flat_x k qb qk (ELit 72)
          && flat_x k hb hk (ELit L) && kzero_x k k hb hk (ELit L)
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
Fixpoint find_zone (k0 k : list kentry) (hb : expr) (hk glast : Z) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (match xlo k0 (eadd (eaddz zb zk) zn) with Some ze => Z.ltb glast ze | None => false end
          && lin_ge0 k0 [(hb, hk)] [(zb, zk)])%bool
      then true else find_zone k0 rest hb hk glast
  | _ :: rest => find_zone k0 rest hb hk glast
  end.
Definition node_rpoison_rel_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    (* [comment removed for export] *)
    let sh := match srl_split k beg 3 with Some e => e | None => mkSrl k beg 3 end in
    let '(hb, hk) := split_lit (eadd (ELit SB) sh) in
    match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp, xhi2 k (eadd beg ne) with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi, Some eh =>
      let glast := SB + (eh - 1) / 8 in
      if (Z.leb 16 nlo && Z.leb nhi (2 ^ 40)
          && (Z.leb eh kLowEnd || (Z.leb kHighBeg blo && Z.leb eh kHighEnd))
          && Z.leb 80 splo && Z.ltb sphi two64
          && Z.ltb glast (splo - 72)
          && Z.leb (rp_chi T + 8) (splo - 72) && Z.leb (rp_cm2 T + 8) (splo - 72) && Z.leb (rp_cm1 T + 8) (splo - 72)
          && Z.leb (rp_csb T + 8) (splo - 72) && Z.leb (rp_ghi T + 8) (splo - 72) && Z.leb (rp_gm2 T + 8) (splo - 72)
          && Z.leb (rp_gm1 T + 8) (splo - 72) && Z.leb (rp_gsb T + 8) (splo - 72)
          && Z.leb 0 (rp_gsb T) && Z.leb 0 (rp_gm1 T) && Z.leb 0 (rp_gm2 T) && Z.leb 0 (rp_ghi T)
          && Z.leb 0 (rp_csb T) && Z.leb 0 (rp_cm1 T) && Z.leb 0 (rp_cm2 T) && Z.leb 0 (rp_chi T)
          && kwritable k k qb qk 72 && flat_x k qb qk (ELit 72)
          && flat_x k hb hk (ELit 1) && find_zone k k hb hk glast
          && img8 k (rp_gsb T) && img8 k (rp_gm1 T) && img8 k (rp_gm2 T) && img8 k (rp_ghi T)
          && img8 k (rp_cm1 T) && img8 k (rp_cm2 T)
          && lit_cell k (rp_csb T) SB && lit_cell k (rp_chi T) kHighEnd
          && Z.ltb (bhi + nhi) two64)%bool
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _, _ => None
    end
  | None => None
  end.
(* [comment removed for export] *)
Definition lit_cellB (bc : AX2B.bctx) (kx : AX2B.kix) (cell v : Z) : bool :=
  if flat_xB bc (ELit 0) cell (ELit 8) then
  match know_lookupBX segs bc kx (ELit 0) cell 8 false [] [] with
  | LHit e sc _ => match sc, AX2B.erangeB bc e with [], Some (lo, hi) => (Z.eqb lo v && Z.eqb hi v)%bool | _, _ => false end
  | _ => false
  end else false.
Lemma lit_cellB_eqf : forall k, lit_cellB (AX2B.mkbc k) (AX2B.mk_kix k) = lit_cell k.
Proof.
  intros k. apply functional_extensionality; intros cell. apply functional_extensionality; intros v.
  unfold lit_cellB, lit_cell. rewrite know_lookupBX_eq, AX2B.know_lookupB_eqf, AX2B.erangeB_eqf, flat_xB_eqf. reflexivity.
Qed.
Definition img8B (bc : AX2B.bctx) (a : Z) : bool := img_covB bc a (a + 8).
Lemma img8B_eqf : forall k, img8B (AX2B.mkbc k) = img8 k.
Proof. intros k. apply functional_extensionality; intros a. unfold img8B, img8. rewrite img_covB_eqf. reflexivity. Qed.
Fixpoint find_zoneB (bc : AX2B.bctx) (k : list kentry) (hb : expr) (hk glast : Z) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (match AX2B.xloB bc (eadd (eaddz zb zk) zn) with Some ze => Z.ltb glast ze | None => false end)
          then AX2B.lin_ge0B bc [(hb, hk)] [(zb, zk)] else false)
      then true else find_zoneB bc rest hb hk glast
  | _ :: rest => find_zoneB bc rest hb hk glast
  end.
Lemma find_zoneB_eq : forall k0 k hb hk glast, find_zoneB (AX2B.mkbc k0) k hb hk glast = find_zone k0 k hb hk glast.
Proof.
  intros k0 k. induction k as [|K rest IH]; intros hb hk glast; [reflexivity|].
  cbn [find_zoneB find_zone]. rewrite !IH, AX2B.xloB_eqf, AX2B.lin_ge0B_eqf. reflexivity.
Qed.
Lemma find_zoneB_eqf : forall k0, find_zoneB (AX2B.mkbc k0) = find_zone k0.
Proof. intros k0. repeat (apply functional_extensionality; intros ?). apply find_zoneB_eq. Qed.
Definition node_rpoison_int (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let bc := AX2B.mkbc k in let kx := AX2B.mk_kix k in
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    let '(bb, bk) := split_lit beg in
    let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8)) (AX2B.mkSrlB bc bb 3)) in
    match AX2B.xloB bc ne, AX2B.xhiB bc ne, AX2B.xloB bc beg, AX2B.xhiB bc beg, AX2B.xloB bc sp, AX2B.xhiB bc sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      let L := (bk + nhi - 1) / 8 - bk / 8 + 1 in
      if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if Z.leb 16 nlo
          then Z.leb nhi (2 ^ 40) else false)
          then (if (if Z.leb (bhi + nhi) kLowEnd then true else (if Z.leb kHighBeg blo then Z.leb (bhi + nhi) kHighEnd else false)) then true else off_bandB bc (a_maps cs) bb bk ne) else false)
          then Z.leb 3 (AX2B.ealignB bc bb) else false)
          then flat_xB bc bb bk (ELit 1) else false)
          then Z.leb 80 splo else false)
          then Z.ltb sphi two64 else false)
          then Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72) else false)
          then Z.leb (rp_chi T + 8) (splo - 72) else false)
          then Z.leb (rp_cm2 T + 8) (splo - 72) else false)
          then Z.leb (rp_cm1 T + 8) (splo - 72) else false)
          then Z.leb (rp_csb T + 8) (splo - 72) else false)
          then Z.leb (rp_ghi T + 8) (splo - 72) else false)
          then Z.leb (rp_gm2 T + 8) (splo - 72) else false)
          then Z.leb (rp_gm1 T + 8) (splo - 72) else false)
          then Z.leb (rp_gsb T + 8) (splo - 72) else false)
          then Z.leb 0 (rp_gsb T) else false)
          then Z.leb 0 (rp_gm1 T) else false)
          then Z.leb 0 (rp_gm2 T) else false)
          then Z.leb 0 (rp_ghi T) else false)
          then Z.leb 0 (rp_csb T) else false)
          then Z.leb 0 (rp_cm1 T) else false)
          then Z.leb 0 (rp_cm2 T) else false)
          then Z.leb 0 (rp_chi T) else false)
          then kwritableB bc k qb qk 72 else false)
          then flat_xB bc qb qk (ELit 72) else false)
          then flat_xB bc hb hk (ELit L) else false)
          then kzero_xB bc k hb hk (ELit L) else false)
          then img8B bc (rp_gsb T) else false)
          then img8B bc (rp_gm1 T) else false)
          then img8B bc (rp_gm2 T) else false)
          then img8B bc (rp_ghi T) else false)
          then img8B bc (rp_cm1 T) else false)
          then img8B bc (rp_cm2 T) else false)
          then lit_cellB bc kx (rp_csb T) SB else false)
          then lit_cellB bc kx (rp_chi T) kHighEnd else false)
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _ => None
    end
  | None => None
  end.
Lemma node_rpoison_int_eq : forall cs, node_rpoison_int cs = node_rpoison_int_ref cs.
Proof.
  intros cs. unfold node_rpoison_int, node_rpoison_int_ref. cbv zeta.
  rewrite ?AX2B.mkSrlB_eqf, ?AX2B.xloB_eqf, ?AX2B.xhiB_eqf, ?AX2B.ealignB_eqf, ?flat_xB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf,
    ?off_bandB_eqf, ?img8B_eqf, ?lit_cellB_eqf. reflexivity.
Qed.
Definition node_rpoison_rel (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let bc := AX2B.mkbc k in let kx := AX2B.mk_kix k in
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    let sh := match srl_split k beg 3 with Some e => e | None => AX2B.mkSrlB bc beg 3 end in
    let '(hb, hk) := split_lit (eadd (ELit SB) sh) in
    match AX2B.xloB bc ne, AX2B.xhiB bc ne, AX2B.xloB bc beg, AX2B.xhiB bc beg, AX2B.xloB bc sp, AX2B.xhiB bc sp, xhi2B bc (eadd beg ne) with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi, Some eh =>
      let glast := SB + (eh - 1) / 8 in
      if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if Z.leb 16 nlo
          then Z.leb nhi (2 ^ 40) else false)
          then (if Z.leb eh kLowEnd then true else (if Z.leb kHighBeg blo then Z.leb eh kHighEnd else false)) else false)
          then Z.leb 80 splo else false)
          then Z.ltb sphi two64 else false)
          then Z.ltb glast (splo - 72) else false)
          then Z.leb (rp_chi T + 8) (splo - 72) else false)
          then Z.leb (rp_cm2 T + 8) (splo - 72) else false)
          then Z.leb (rp_cm1 T + 8) (splo - 72) else false)
          then Z.leb (rp_csb T + 8) (splo - 72) else false)
          then Z.leb (rp_ghi T + 8) (splo - 72) else false)
          then Z.leb (rp_gm2 T + 8) (splo - 72) else false)
          then Z.leb (rp_gm1 T + 8) (splo - 72) else false)
          then Z.leb (rp_gsb T + 8) (splo - 72) else false)
          then Z.leb 0 (rp_gsb T) else false)
          then Z.leb 0 (rp_gm1 T) else false)
          then Z.leb 0 (rp_gm2 T) else false)
          then Z.leb 0 (rp_ghi T) else false)
          then Z.leb 0 (rp_csb T) else false)
          then Z.leb 0 (rp_cm1 T) else false)
          then Z.leb 0 (rp_cm2 T) else false)
          then Z.leb 0 (rp_chi T) else false)
          then kwritableB bc k qb qk 72 else false)
          then flat_xB bc qb qk (ELit 72) else false)
          then flat_xB bc hb hk (ELit 1) else false)
          then find_zoneB bc k hb hk glast else false)
          then img8B bc (rp_gsb T) else false)
          then img8B bc (rp_gm1 T) else false)
          then img8B bc (rp_gm2 T) else false)
          then img8B bc (rp_ghi T) else false)
          then img8B bc (rp_cm1 T) else false)
          then img8B bc (rp_cm2 T) else false)
          then lit_cellB bc kx (rp_csb T) SB else false)
          then lit_cellB bc kx (rp_chi T) kHighEnd else false)
          then Z.ltb (bhi + nhi) two64 else false)
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _, _ => None
    end
  | None => None
  end.
Lemma node_rpoison_rel_eq : forall cs, node_rpoison_rel cs = node_rpoison_rel_ref cs.
Proof.
  intros cs. unfold node_rpoison_rel, node_rpoison_rel_ref. cbv zeta.
  rewrite ?AX2B.mkSrlB_eqf, ?AX2B.xloB_eqf, ?AX2B.xhiB_eqf, ?xhi2B_eqf, ?flat_xB_eqf, ?kwritableB_eqf,
    ?find_zoneB_eqf, ?img8B_eqf, ?lit_cellB_eqf. reflexivity.
Qed.

Definition node_rpoison (cs : acs) : option acs :=
  match node_rpoison_int cs with Some cs' => Some cs' | None => node_rpoison_rel cs end.

(* [comment removed for export] *)
Definition rc_regs (sr : list expr) (e1 e2 e3 e20 : expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 11 e1) 12 e2) 13 e3) 14 (ELit 0)) 15 (ELit 0)) 20 e20.
Definition node_readcheck (cs : acs) : option acs :=
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
    let '(bb, bk) := split_lit beg in
    let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8)) (mkSrl k bb 3)) in
    match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      let L := (bk + nhi - 1) / 8 - bk / 8 + 1 in
      first_false 1 [Z.leb 16 nlo; Z.leb nhi (2 ^ 40);
        (Z.leb (bhi + nhi) kLowEnd || (Z.leb kHighBeg blo && Z.leb (bhi + nhi) kHighEnd) || off_band k (a_maps cs) bb bk ne);
        Z.leb 3 (ealign k bb); flat_x k bb bk (ELit 1); Z.leb 80 splo; Z.ltb sphi two64;
        Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72); Z.leb (rp_chi T + 8) (splo - 72);
        kwritable k k qb qk 72; flat_x k qb qk (ELit 72); flat_x k hb hk (ELit L); kzero_x k k hb hk (ELit L);
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
  else None.
End WithSegs.
End RPN.
