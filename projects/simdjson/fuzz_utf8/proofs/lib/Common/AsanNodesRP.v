(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
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
  rp_ghi : Z; rp_chi : Z      (* [comment removed for export] *)
}.
Definition RP_ASAN : rptab := RPT 0xcdd4c 0x6785c 0x678b4 0x1432e8 0x14bf00 0x1432f0 0x14cbf0 0x1432f8 0x14cbf8 0x143300 0x14cbe8.
Definition RP_BOTH : rptab := RPT 0xcdd3c 0x6784c 0x678a4 0x143370 0x14bf80 0x143378 0x14cc70 0x143380 0x14cc78 0x143388 0x14cc68. (* [comment removed for export] *)

Definition SB : Z := 0x7fff8000.
Definition kLowEnd : Z := 0x7fff7fff.
Definition kHighBeg : Z := 0x10007fff8000.
Definition kHighEnd : Z := 0x7fffffffffff.
(* [comment removed for export] *)
Definition BAND_LO : Z := 0x7fff7000.
Definition BAND_LEN : Z := kHighBeg - BAND_LO.

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
(* [comment removed for export] *)
Definition img8 (k : list kentry) (a : Z) : bool := img_cov k a (a + 8).

(* [comment removed for export] *)
Definition in_app_mem (k : list kentry) (bb : expr) (bk blo bhi nhi : Z) : bool :=
  (Z.leb (bhi + nhi) kLowEnd || (Z.leb kHighBeg blo && Z.leb (bhi + nhi) kHighEnd)
   || (ranges_apart_x k (ELit 0) BAND_LO (ELit BAND_LEN) bb bk (ELit nhi) && Z.leb 0 nhi && Z.leb (bhi + nhi) kHighEnd))%bool.

Definition node_rpoison (cs : acs) : option acs :=
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
          && in_app_mem k bb bk blo bhi nhi
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
        in_app_mem k bb bk blo bhi nhi;
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
