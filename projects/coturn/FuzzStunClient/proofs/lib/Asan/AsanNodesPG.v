(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore AsanNodesRP AsanPGVal FContractAsan AsanNodesFX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AsanPGVal.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module PGN.
Definition SB : Z := RPN.SB.

(* [comment removed for export] *)
Definition pgsel := PGV.pgsel.
Definition zero_diff := PGV.zero_diff.
Definition pg_match := PGV.pg_match.
Definition strip_b1 := PGV.strip_b1.
Definition partial_val_ok := PGV.partial_val_ok.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : N.
Variable T : RPN.rptab.
(* [comment removed for export] *)
Definition ISRC_ENTRY : Z := RPN.rp_isrc T.    (* [comment removed for export] *)
Definition ISRC_EXIT : Z := RPN.rp_isrcx T.    (* [comment removed for export] *)
Definition IDST_ENTRY : Z := RPN.rp_idst T.    (* [comment removed for export] *)
Definition IDST_EXIT : Z := RPN.rp_idstx T.    (* [comment removed for export] *)

Fixpoint first_false (i : nat) (l : list bool) : nat :=
  match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.

(* [comment removed for export] *)
Definition region_exit (cs : acs) (exitpc : Z) (rs : list nat) (k' : list kentry) : acs :=
  let nx := nxt cs in
  with_ss cs (mk_ss exitpc (sr_fresh (s_regs (a_ss cs)) rs nx) k' (nx + N.of_nat (length rs))).

(* [comment removed for export] *)
Definition PG_ENTRY : Z := RPN.rp_pg T.    (* [comment removed for export] *)
Definition PG_EXIT : Z := RPN.rp_pgx T.    (* [comment removed for export] *)
Definition PG_REGS : list nat := [1; 10; 11; 12; 13; 14; 15; 16; 17; 22]%nat.
Definition pg_tests (cs : acs) : option (list bool) :=
  let k := kn cs in
  let ne := reg cs 9 in let s6 := reg cs 22 in let p := reg cs 20 in
  let '(hb, hk) := split_lit (eadd (mkSrl k p 3) (ELit SB)) in
  let '(pb, pk) := split_lit (eadd (eadd (mkSrl k p 3) (ELit SB)) (mkSrl k ne 3)) in
  match xlo k ne, xhi k ne, xlo k p, xhi k p with
  | Some nlo, Some nhi, Some plo, Some phi =>
    Some [ zero_diff k s6 (EMd M_MUL (ELit 8) (mkSrl k ne 3))
         ; flat_x k pb pk (ELit 1); kn_vars_lt (nxt cs) (kn_havoc_led k (a_maps cs) pb pk (ELit 1)); expr_vars_lt (nxt cs) pb   (* [comment removed for export] *)
         ; Z.leb 1 nlo; Z.leb 3 (ealign k p)
         ; (Z.leb RPN.kHighBeg plo && Z.leb (phi + nhi) RPN.kHighEnd) || off_band k (a_maps cs) p 0 ne   (* [comment removed for export] *)
         ; Z.leb 0 plo
         ; Z.leb 0 (RPN.rp_gsb T); Z.leb 0 (RPN.rp_csb T); Z.leb 0 (RPN.rp_gm1 T); Z.leb 0 (RPN.rp_cm1 T)
         ; Z.leb 0 (RPN.rp_gm2 T); Z.leb 0 (RPN.rp_cm2 T); Z.leb 0 (RPN.rp_ghi T); Z.leb 0 (RPN.rp_chi T); Z.leb 0 (RPN.rp_gfl T)
         ; RPN.img8 k (RPN.rp_gsb T); RPN.img8 k (RPN.rp_gm1 T); RPN.img8 k (RPN.rp_gm2 T); RPN.img8 k (RPN.rp_ghi T)
         ; RPN.img8 k (RPN.rp_cm1 T); RPN.img8 k (RPN.rp_cm2 T); RPN.img8 k (RPN.rp_gfl T)
         ; RPN.lit_cell segs k (RPN.rp_csb T) SB; RPN.lit_cell segs k (RPN.rp_chi T) RPN.kHighEnd
         ; FN.cell_is segs k (ELit 0) (RPN.rp_cfl T + 85) 1 1; FN.cell_is segs k (ELit 0) (RPN.rp_ccp T) 1 1
         ; kwritable_x k k hb hk (eaddz (mkSrl k ne 3) 1); flat_x k hb hk (eaddz (mkSrl k ne 3) 1)   (* [comment removed for export] *)
         ; fresh_ok nx0 cs ]%bool
  | _, _, _, _ => None
  end.
Definition node_pgran_ref (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
    if negb (Z.eqb (pc cs) PG_ENTRY) then None else
    match pg_tests cs with
    | Some ts =>
        if forallb (fun b : bool => b) ts then
          let k := kn cs in
          let ne := reg cs 9 in let p := reg cs 20 in
          let '(pb, pk) := split_lit (eadd (eadd (mkSrl k p 3) (ELit SB)) (mkSrl k ne 3)) in
          let nx := nxt cs in
          let k' := KWord (SA pb pk) 1 (pgsel ne (EVar nx)) :: kn_havoc_led k (a_maps cs) pb pk (ELit 1) in   (* [comment removed for export] *)
          Some (with_ss cs (mk_ss PG_EXIT (sr_fresh (s_regs (a_ss cs)) PG_REGS (N.succ nx)) k' (N.succ nx + N.of_nat (length PG_REGS))))
        else None
    | None => None
    end
  | _ => None
  end.
(* [comment removed for export] *)
Definition pg_testsH (cs : acs) (kh : list kentry) : option (list bool) :=
  let k := kn cs in
  let ne := reg cs 9 in let s6 := reg cs 22 in let p := reg cs 20 in
  let '(hb, hk) := split_lit (eadd (mkSrl k p 3) (ELit SB)) in
  let '(pb, pk) := split_lit (eadd (eadd (mkSrl k p 3) (ELit SB)) (mkSrl k ne 3)) in
  match xlo k ne, xhi k ne, xlo k p, xhi k p with
  | Some nlo, Some nhi, Some plo, Some phi =>
    Some [ zero_diff k s6 (EMd M_MUL (ELit 8) (mkSrl k ne 3))
         ; flat_x k pb pk (ELit 1); kn_vars_lt (nxt cs) kh; expr_vars_lt (nxt cs) pb
         ; Z.leb 1 nlo; Z.leb 3 (ealign k p)
         ; off_bandL k (a_maps cs) p 0 ne (Z.leb RPN.kHighBeg plo && Z.leb (phi + nhi) RPN.kHighEnd)   (* [comment removed for export] *)
         ; Z.leb 0 plo
         ; Z.leb 0 (RPN.rp_gsb T); Z.leb 0 (RPN.rp_csb T); Z.leb 0 (RPN.rp_gm1 T); Z.leb 0 (RPN.rp_cm1 T)
         ; Z.leb 0 (RPN.rp_gm2 T); Z.leb 0 (RPN.rp_cm2 T); Z.leb 0 (RPN.rp_ghi T); Z.leb 0 (RPN.rp_chi T); Z.leb 0 (RPN.rp_gfl T)
         ; RPN.img8 k (RPN.rp_gsb T); RPN.img8 k (RPN.rp_gm1 T); RPN.img8 k (RPN.rp_gm2 T); RPN.img8 k (RPN.rp_ghi T)
         ; RPN.img8 k (RPN.rp_cm1 T); RPN.img8 k (RPN.rp_cm2 T); RPN.img8 k (RPN.rp_gfl T)
         ; RPN.lit_cell segs k (RPN.rp_csb T) SB; RPN.lit_cell segs k (RPN.rp_chi T) RPN.kHighEnd
         ; FN.cell_is segs k (ELit 0) (RPN.rp_cfl T + 85) 1 1; FN.cell_is segs k (ELit 0) (RPN.rp_ccp T) 1 1
         ; kwritable_x k k hb hk (eaddz (mkSrl k ne 3) 1); flat_x k hb hk (eaddz (mkSrl k ne 3) 1)
         ; fresh_ok nx0 cs ]%bool
  | _, _, _, _ => None
  end.
Definition node_pgran (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
    if negb (Z.eqb (pc cs) PG_ENTRY) then None else
    let k := kn cs in
    let ne := reg cs 9 in let p := reg cs 20 in
    let '(pb, pk) := split_lit (eadd (eadd (mkSrl k p 3) (ELit SB)) (mkSrl k ne 3)) in
    let kh := kn_havoc_ledB (AX2B.mkbc k) (a_maps cs) pb pk (ELit 1) in
    match pg_testsH cs kh with
    | Some ts =>
        if forallb (fun b : bool => b) ts then
          let nx := nxt cs in
          Some (with_ss cs (mk_ss PG_EXIT (sr_fresh (s_regs (a_ss cs)) PG_REGS (N.succ nx)) (KWord (SA pb pk) 1 (pgsel ne (EVar nx)) :: kh) (N.succ nx + N.of_nat (length PG_REGS))))
        else None
    | None => None
    end
  | _ => None
  end.
Lemma node_pgran_eq : forall cs args, node_pgran cs args = node_pgran_ref cs args.
Proof.
  intros cs args. unfold node_pgran, node_pgran_ref. destruct args; [|reflexivity].
  destruct (negb (Z.eqb (pc cs) PG_ENTRY)); [reflexivity|].
  rewrite kn_havoc_ledB_eqf. unfold pg_testsH, pg_tests. cbv zeta.
  destruct (split_lit (eadd (eadd (mkSrl (kn cs) (reg cs 20) 3) (ELit SB)) (mkSrl (kn cs) (reg cs 9) 3))) as [pb pk].
  destruct (split_lit (eadd (mkSrl (kn cs) (reg cs 20) 3) (ELit SB))) as [hb hk].
  destruct (xlo (kn cs) (reg cs 9)), (xhi (kn cs) (reg cs 9)), (xlo (kn cs) (reg cs 20)), (xhi (kn cs) (reg cs 20)); try reflexivity.
  rewrite off_bandL_or. reflexivity.
Qed.
Definition diag_pgran (cs : acs) (args : list expr) : nat :=
  if negb (Z.eqb (pc cs) PG_ENTRY) then 100%nat else
  match pg_tests cs with Some ts => first_false 1 ts | None => 102%nat end.

(* [comment removed for export] *)
Definition ISRC_REGS : list nat := [13; 14; 15; 16; 19]%nat.
Definition node_isrc (cs : acs) (args : list expr) : option acs :=
  match args with
  | [eB; ELit N] =>
    let k := kn cs in
    if negb (Z.eqb (pc cs) ISRC_ENTRY) then None else
    let src := reg cs 11 in let s3 := reg cs 19 in
    let '(sb, sk) := split_lit (eadd (mkSrl k eB 3) (ELit SB)) in
    let sn := ELit (N / 8) in
    match xhi k src, xlo k s3, xhi k s3 with
    | Some shi, Some s3lo, Some s3hi =>
      if (Z.leb 6 (ealign k eB) && Z.eqb (N mod 64) 0 && Z.ltb 0 N && Z.ltb N (2 ^ 40)
          && flat_x k eB 0 (ELit N)
          && Z.leb 1 s3lo && Z.ltb s3hi two64 && Z.ltb shi two64
          && lin_ge0 k [(src, 0)] [(eB, 0)]                 (* [comment removed for export] *)
          && lin_ge0 k [(eB, N - 1)] [(src, 0)]             (* [comment removed for export] *)
          && lin_ge0 k [(s3, -1)] [(eB, 0)]                 (* [comment removed for export] *)
          && lin_ge0 k [(eB, N)] [(s3, 0)]                  (* [comment removed for export] *)
          && flat_x k sb sk sn && kzero_x k k sb sk sn
          && Z.leb 0 (RPN.rp_gsb T) && Z.leb 0 (RPN.rp_csb T)
          && RPN.img8 k (RPN.rp_gsb T) && RPN.lit_cell segs k (RPN.rp_csb T) SB
          && fresh_ok nx0 cs)%bool
      then Some (region_exit cs ISRC_EXIT ISRC_REGS k)
      else None
    | _, _, _ => None
    end
  | _ => None
  end.

(* [comment removed for export] *)
Definition IDST_REGS : list nat := [13; 14; 15; 16; 17; 20]%nat.
Definition idst_tests (cs : acs) : option (list bool) :=
  let k := kn cs in
  let dst := reg cs 10 in let ne := reg cs 12 in let s4 := reg cs 20 in
  let '(hb, hk) := split_lit (eadd (mkSrl k dst 3) (ELit SB)) in
  let hn := mkSrl k ne 3 in
  let '(pb, pk) := split_lit (eadd (eadd (mkSrl k dst 3) (ELit SB)) hn) in
  match xlo k ne, xhi k ne, xhi k dst with
  | Some nlo, Some nhi, Some dhi =>
    Some [ Z.leb 3 (ealign k dst); Z.leb 1 nlo; Z.leb nhi 64; Z.ltb (dhi + 64) (2 ^ 47)
         ; flat_x k dst 0 ne
         ; lin_ge0 k [(s4, 0)] [(dst, 0); (ne, 0)]; lin_ge0 k [(dst, 0); (ne, 0)] [(s4, 0)]
         ; Z.ltb nhi 8 || (flat_x k hb hk hn && kzero_x k k hb hk hn)
         ; match lowbits k ne 3 with
           | Some 0 => true
           | _ => flat_x k pb pk (ELit 1) &&
                  match know_lookup segs k pb pk 1 false [] [] with
                  | LHit v sc _ => match sc with [] => partial_val_ok k ne v | _ => false end
                  | _ => false
                  end
           end
         ; Z.leb 3 (ealign k hb); FN.rw_lit k hb (hk - hk mod 8) 16
         ; Z.leb 0 (RPN.rp_gsb T); Z.leb 0 (RPN.rp_csb T); RPN.img8 k (RPN.rp_gsb T); RPN.lit_cell segs k (RPN.rp_csb T) SB
         ; fresh_ok nx0 cs ]%bool
  | _, _, _ => None
  end.
Definition node_idst (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
    if negb (Z.eqb (pc cs) IDST_ENTRY) then None else
    match idst_tests cs with
    | Some ts => if forallb (fun b : bool => b) ts then Some (region_exit cs IDST_EXIT IDST_REGS (kn cs)) else None
    | None => None
    end
  | _ => None
  end.
Definition diag_idst (cs : acs) (args : list expr) : nat :=
  if negb (Z.eqb (pc cs) IDST_ENTRY) then 100%nat else
  match idst_tests cs with Some ts => first_false 1 ts | None => 102%nat end.

(* [comment removed for export] *)
Definition rpp_tests (cs : acs) (ret : Z) : option (list bool * expr * Z) :=
  let k := kn cs in
  let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
  let '(qb, qk) := split_lit (eaddz sp (-72)) in
  let '(hb, hk) := split_lit (eadd (mkSrl k beg 3) (ELit SB)) in
  let hn := mkSrl k ne 3 in
  let '(pb, pk) := split_lit (eadd (eadd (mkSrl k beg 3) (ELit SB)) hn) in
  match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
  | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
    Some ([ Z.leb 16 nlo; Z.leb nhi (2 ^ 40); Z.leb 3 (ealign k beg)
          ; off_bandL k (a_maps cs) beg 0 ne (Z.leb RPN.kHighBeg blo && Z.leb (bhi + nhi) RPN.kHighEnd)   (* [comment removed for export] *)
          ; Z.leb 0 blo
          ; Z.leb 80 splo; Z.ltb sphi two64
          ; Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72)
          ; Z.leb (RPN.rp_chi T + 8) (splo - 72); Z.leb (RPN.rp_cm2 T + 8) (splo - 72); Z.leb (RPN.rp_cm1 T + 8) (splo - 72)
          ; Z.leb (RPN.rp_csb T + 8) (splo - 72); Z.leb (RPN.rp_ghi T + 8) (splo - 72); Z.leb (RPN.rp_gm2 T + 8) (splo - 72)
          ; Z.leb (RPN.rp_gm1 T + 8) (splo - 72); Z.leb (RPN.rp_gsb T + 8) (splo - 72)
          ; Z.leb 0 (RPN.rp_gsb T); Z.leb 0 (RPN.rp_gm1 T); Z.leb 0 (RPN.rp_gm2 T); Z.leb 0 (RPN.rp_ghi T)
          ; Z.leb 0 (RPN.rp_csb T); Z.leb 0 (RPN.rp_cm1 T); Z.leb 0 (RPN.rp_cm2 T); Z.leb 0 (RPN.rp_chi T)
          ; kwritable k k qb qk 72; flat_x k qb qk (ELit 72)
          ; flat_x k hb hk hn; kzero_x k k hb hk hn
          ; match lowbits k ne 3 with
            | Some 0 => true
            | _ => flat_x k pb pk (ELit 1) &&
                   match know_lookup segs k pb pk 1 false [] [] with
                   | LHit v sc _ => match sc with [] => partial_val_ok k ne v | _ => false end
                   | _ => false
                   end
            end
          ; RPN.img8 k (RPN.rp_gsb T); RPN.img8 k (RPN.rp_gm1 T); RPN.img8 k (RPN.rp_gm2 T); RPN.img8 k (RPN.rp_ghi T)
          ; RPN.img8 k (RPN.rp_cm1 T); RPN.img8 k (RPN.rp_cm2 T)
          ; RPN.lit_cell segs k (RPN.rp_csb T) SB; RPN.lit_cell segs k (RPN.rp_chi T) RPN.kHighEnd ]%bool, qb, qk)
  | _, _, _, _, _, _ => None
  end.
Definition node_rppart (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
    if negb (Z.eqb (pc cs) (RPN.rp_entry T)) then None else
    match ret_lit cs with
    | Some ret =>
      match rpp_tests cs ret with
      | Some (ts, qb, qk) =>
          if forallb (fun b : bool => b) ts then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc (kn cs) qb qk (ELit 72)) else None
      | None => None
      end
    | None => None
    end
  | _ => None
  end.
Definition diag_rppart (cs : acs) (args : list expr) : nat :=
  if negb (Z.eqb (pc cs) (RPN.rp_entry T)) then 100%nat else
  match ret_lit cs with
  | Some ret => match rpp_tests cs ret with Some (ts, _, _) => first_false 1 ts | None => 102%nat end
  | None => 101%nat
  end.

(* [comment removed for export] *)
Definition rpin_tests (cs : acs) (eB : expr) (N : Z) : option (list bool * expr * Z) :=
  let k := kn cs in
  let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
  let '(qb, qk) := split_lit (eaddz sp (-72)) in
  let '(hb, hk) := split_lit (eadd (mkSrl k eB 3) (ELit SB)) in
  let hn := ELit (N / 8) in
  match xlo k ne, xhi k ne, xlo k eB, xhi k eB, xlo k sp, xhi k sp with
  | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
    Some ([ Z.leb 16 nlo; Z.leb nhi (2 ^ 40); Z.leb 3 (ealign k eB); Z.eqb (N mod 8) 0; Z.ltb 0 N
          ; off_bandL k (a_maps cs) eB 0 (ELit N) (Z.leb RPN.kHighBeg blo && Z.leb (bhi + N) RPN.kHighEnd)   (* [comment removed for export] *)
          ; Z.ltb N (2 ^ 47)
          ; Z.leb 80 splo; Z.ltb sphi two64
          ; Z.ltb (SB + (bhi + N - 1) / 8) (splo - 72)
          ; Z.leb (RPN.rp_chi T + 8) (splo - 72); Z.leb (RPN.rp_cm2 T + 8) (splo - 72); Z.leb (RPN.rp_cm1 T + 8) (splo - 72)
          ; Z.leb (RPN.rp_csb T + 8) (splo - 72); Z.leb (RPN.rp_ghi T + 8) (splo - 72); Z.leb (RPN.rp_gm2 T + 8) (splo - 72)
          ; Z.leb (RPN.rp_gm1 T + 8) (splo - 72); Z.leb (RPN.rp_gsb T + 8) (splo - 72)
          ; Z.leb 0 (RPN.rp_gsb T); Z.leb 0 (RPN.rp_gm1 T); Z.leb 0 (RPN.rp_gm2 T); Z.leb 0 (RPN.rp_ghi T)
          ; Z.leb 0 (RPN.rp_csb T); Z.leb 0 (RPN.rp_cm1 T); Z.leb 0 (RPN.rp_cm2 T); Z.leb 0 (RPN.rp_chi T)
          ; kwritable k k qb qk 72; flat_x k qb qk (ELit 72)
          ; flat_x k eB 0 (ELit N); lin_ge0 k [(beg, 0)] [(eB, 0)]; lin_ge0 k [(eB, N)] [(beg, 0); (ne, 0)]
          ; flat_x k hb hk hn; kzero_x k k hb hk hn
          ; RPN.img8 k (RPN.rp_gsb T); RPN.img8 k (RPN.rp_gm1 T); RPN.img8 k (RPN.rp_gm2 T); RPN.img8 k (RPN.rp_ghi T)
          ; RPN.img8 k (RPN.rp_cm1 T); RPN.img8 k (RPN.rp_cm2 T)
          ; RPN.lit_cell segs k (RPN.rp_csb T) SB; RPN.lit_cell segs k (RPN.rp_chi T) RPN.kHighEnd ]%bool, qb, qk)
  | _, _, _, _, _, _ => None
  end.
(* [comment removed for export] *)
Definition rpin_testsS (cs : acs) (eB eN : expr) : option (list bool * expr * Z) :=
  let k := kn cs in
  let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
  let '(qb, qk) := split_lit (eaddz sp (-72)) in
  let '(hb, hk) := split_lit (eadd (mkSrl k eB 3) (ELit SB)) in
  let hn := mkSrl k eN 3 in
  match xlo k ne, xhi k ne, xlo k eB, xhi k eB, xlo k sp, xhi k sp, xlo k eN, xhi k eN with
  | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi, Some Nlo, Some Nhi =>
    Some ([ Z.leb 16 nlo; Z.leb nhi (2 ^ 40); Z.leb 3 (ealign k eB); Z.leb 3 (ealign k eN); Z.leb 1 Nlo
          ; off_bandL k (a_maps cs) eB 0 eN (Z.leb RPN.kHighBeg blo && Z.leb (bhi + Nhi) RPN.kHighEnd)   (* [comment removed for export] *)
          ; Z.ltb Nhi (2 ^ 47)
          ; Z.leb 80 splo; Z.ltb sphi two64
          ; Z.ltb (SB + (bhi + Nhi - 1) / 8) (splo - 72)
          ; Z.leb (RPN.rp_chi T + 8) (splo - 72); Z.leb (RPN.rp_cm2 T + 8) (splo - 72); Z.leb (RPN.rp_cm1 T + 8) (splo - 72)
          ; Z.leb (RPN.rp_csb T + 8) (splo - 72); Z.leb (RPN.rp_ghi T + 8) (splo - 72); Z.leb (RPN.rp_gm2 T + 8) (splo - 72)
          ; Z.leb (RPN.rp_gm1 T + 8) (splo - 72); Z.leb (RPN.rp_gsb T + 8) (splo - 72)
          ; Z.leb 0 (RPN.rp_gsb T); Z.leb 0 (RPN.rp_gm1 T); Z.leb 0 (RPN.rp_gm2 T); Z.leb 0 (RPN.rp_ghi T)
          ; Z.leb 0 (RPN.rp_csb T); Z.leb 0 (RPN.rp_cm1 T); Z.leb 0 (RPN.rp_cm2 T); Z.leb 0 (RPN.rp_chi T)
          ; kwritable k k qb qk 72; flat_x k qb qk (ELit 72)
          ; lin_ge0 k [(beg, 0)] [(eB, 0)]; lin_ge0 k [(eB, 0); (eN, 0)] [(beg, 0); (ne, 0)]
          ; flat_x k hb hk hn; kzero_x k k hb hk hn
          ; RPN.img8 k (RPN.rp_gsb T); RPN.img8 k (RPN.rp_gm1 T); RPN.img8 k (RPN.rp_gm2 T); RPN.img8 k (RPN.rp_ghi T)
          ; RPN.img8 k (RPN.rp_cm1 T); RPN.img8 k (RPN.rp_cm2 T)
          ; RPN.lit_cell segs k (RPN.rp_csb T) SB; RPN.lit_cell segs k (RPN.rp_chi T) RPN.kHighEnd ]%bool, qb, qk)
  | _, _, _, _, _, _, _, _ => None
  end.
Definition node_rpinS (cs : acs) (eB eN : expr) : option acs :=
    if negb (Z.eqb (pc cs) (RPN.rp_entry T)) then None else
    match ret_lit cs with
    | Some ret =>
      match rpin_testsS cs eB eN with
      | Some (ts, qb, qk) =>
          if forallb (fun b : bool => b) ts then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc (kn cs) qb qk (ELit 72)) else None
      | None => None
      end
    | None => None
    end.
Definition node_rpin (cs : acs) (args : list expr) : option acs :=
  match args with
  | [eB; ELit N] =>
    if negb (Z.eqb (pc cs) (RPN.rp_entry T)) then None else
    match ret_lit cs with
    | Some ret =>
      match rpin_tests cs eB N with
      | Some (ts, qb, qk) =>
          if forallb (fun b : bool => b) ts then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc (kn cs) qb qk (ELit 72)) else None
      | None => None
      end
    | None => None
    end
  | [eB; eN] => node_rpinS cs eB eN   (* [comment removed for export] *)
  | _ => None
  end.
Definition diag_rpin (cs : acs) (args : list expr) : nat :=
  match args with
  | [eB; ELit N] =>
    if negb (Z.eqb (pc cs) (RPN.rp_entry T)) then 100%nat else
    match ret_lit cs with
    | Some ret => match rpin_tests cs eB N with Some (ts, _, _) => first_false 1 ts | None => 102%nat end
    | None => 101%nat
    end
  | [eB; eN] =>   (* [comment removed for export] *)
    if negb (Z.eqb (pc cs) (RPN.rp_entry T)) then 100%nat else
    match ret_lit cs with
    | Some ret => match rpin_testsS cs eB eN with Some (ts, _, _) => first_false 1 ts | None => 102%nat end
    | None => 101%nat
    end
  | _ => 103%nat
  end.

(* [comment removed for export] *)
Fixpoint respell8 (k : list kentry) (e : expr) : expr :=
  match e with
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb (c mod two64) (two64 - 8) then EMd M_MUL (ELit 8) (mkSrl k (respell8 k a) 3) else EAlu ALU_AND (respell8 k a) (ELit c)
  | EAlu op a b => EAlu op (respell8 k a) (respell8 k b)
  | EMd op a b => EMd op (respell8 k a) (respell8 k b)
  | _ => e
  end.
Definition node_and2srl (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit r] =>
    if negb (Z.leb 1 r && Z.ltb r 32)%bool then None else
    Some (set_reg cs (Z.to_nat r) (respell8 (kn cs) (reg cs (Z.to_nat r))))
  | _ => None
  end.

(* [comment removed for export] *)
Definition diag_isrc (cs : acs) (args : list expr) : nat :=
  match args with
  | [eB; ELit N] =>
    let k := kn cs in
    if negb (Z.eqb (pc cs) ISRC_ENTRY) then 100%nat else
    let src := reg cs 11 in let s3 := reg cs 19 in
    let '(sb, sk) := split_lit (eadd (mkSrl k eB 3) (ELit SB)) in
    let sn := ELit (N / 8) in
    match xhi k src, xlo k s3, xhi k s3 with
    | Some shi, Some s3lo, Some s3hi =>
      first_false 1 [Z.leb 6 (ealign k eB); Z.eqb (N mod 64) 0; Z.ltb 0 N; Z.ltb N (2 ^ 40); flat_x k eB 0 (ELit N);
        Z.leb 1 s3lo; Z.ltb s3hi two64; Z.ltb shi two64;
        lin_ge0 k [(src, 0)] [(eB, 0)]; lin_ge0 k [(eB, N - 1)] [(src, 0)]; lin_ge0 k [(s3, -1)] [(eB, 0)]; lin_ge0 k [(eB, N)] [(s3, 0)];
        flat_x k sb sk sn; kzero_x k k sb sk sn; Z.leb 0 (RPN.rp_gsb T); Z.leb 0 (RPN.rp_csb T);
        RPN.img8 k (RPN.rp_gsb T); RPN.lit_cell segs k (RPN.rp_csb T) SB; fresh_ok nx0 cs]%bool
    | _, _, _ => 102%nat
    end
  | _ => 101%nat
  end.

(* [comment removed for export] *)
Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 105 then node_pgran cs args
  else if Nat.eqb id 106 then node_isrc cs args
  else if Nat.eqb id 107 then node_idst cs args
  else if Nat.eqb id 108 then node_rppart cs args
  else if Nat.eqb id 109 then node_and2srl cs args
  else if Nat.eqb id 110 then node_rpin cs args
  else None.
End WithSegs.
End PGN.
