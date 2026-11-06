(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanPrintfBufSpec.
Import ListNotations.
Import AX2. Import APC.
Unset Lia Cache.
Open Scope Z_scope.

Module PFN.
Section WithFP1. Context {FP : PropExec.FPState}.
(* [comment removed for export] *)
Definition pftab_of (A : atable) : apftab := if Z.eqb (x_memcpy A) 0x116748 then APF_ASAN else APF_BOTH.

(* [comment removed for export] *)
Fixpoint kn_havocs (k : list kentry) (rs : list (expr * Z * expr)) : list kentry :=
  match rs with
  | [] => k
  | (b, o, n) :: rest => kn_havocs (kn_havoc k b o n) rest
  end.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.
Variable T : apftab.

(* [comment removed for export] *)
Definition lit_cellw (k : list kentry) (cell : Z) (w : nat) (v : Z) : bool :=
  flat_x k (ELit 0) cell (ELit (Z.of_nat w)) &&
  match know_lookup segs k (ELit 0) cell w false [] [] with
  | LHit e sc _ => match sc, erange k e with [], Some (lo, hi) => Z.eqb lo v && Z.eqb hi v | _, _ => false end
  | _ => false
  end.

(* [comment removed for export] *)
Definition cell_val8 (k : list kentry) (cell : Z) : option Z :=
  if flat_x k (ELit 0) cell (ELit 8) then
    match know_lookup segs k (ELit 0) cell 8 false [] [] with
    | LHit e sc _ => match sc, erange k e with [], Some (lo, hi) => if Z.eqb lo hi then Some lo else None | _, _ => None end
    | _ => None
    end
  else None.

(* [comment removed for export] *)
Definition cell_any8 (k : list kentry) (cell : Z) : bool :=
  flat_x k (ELit 0) cell (ELit 8) &&
  match know_lookup segs k (ELit 0) cell 8 false [] [] with
  | LHit _ sc _ => match sc with [] => true | _ => false end
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint kzero_lit (k : list kentry) (lo hi : Z) : bool :=
  match k with
  | [] => false
  | KZero (SA (ELit 0) o) (ELit L) :: rest =>
      (Z.leb 0 o && Z.leb 0 L && Z.ltb (o + L) two64 && Z.leb o lo && Z.leb hi (o + L)) || kzero_lit rest lo hi
  | _ :: rest => kzero_lit rest lo hi
  end.

(* [comment removed for export] *)
Definition is_zero (k : list kentry) (e : expr) : bool :=
  match erange k e with Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0 | None => false end.

(* [comment removed for export] *)
Definition cells_ok (k : list kentry) : bool :=
  (lit_cellw k (apf_rvp T) 8 (apf_vp T) && lit_cellw k (apf_rvfp T) 8 (apf_vfp T)
   && lit_cellw k (apf_rmc T) 8 (apf_mc T) && lit_cellw k (apf_rms T) 8 (apf_ms T)
   && lit_cellw k (apf_init T) 1 1 && lit_cellw k (apf_init T + 1) 1 1 && lit_cellw k (apf_chkpf T) 1 1
   && lit_cellw k (apf_sbc T) 8 APF_SB
   && lit_cellw k (apf_file T) 4 5 && lit_cellw k (apf_file T + 32) 8 (apf_buf T + 1024)
   && lit_cellw k (apf_file T + 96) 8 1024
   && lit_cellw k (apf_file T + 140) 4 0xffffffff && lit_cellw k (apf_file T + 144) 4 0xffffffff
   && cell_any8 k (apf_canc T))%bool.

Definition node_printfd (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (apf_entry T)) then None else
  match ret_lit cs, cell_val8 k (apf_file T + 40) with
  | Some ret, Some w =>
    let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (- APF_WIN)) in
    match xlo k sp, xhi k sp with
    | Some splo, Some sphi =>
      if (is_zero k (reg cs 11)
          && Z.leb 4 (ealign k sp) && Z.leb (2 ^ 46) splo && Z.leb sphi 0x7fffffffffff
          && kwritable k k qb qk APF_WIN && flat_x k qb qk (ELit APF_WIN)
          && fresh_ok nx0 cs
          && img_cov k 0x10000 0x4b000 && img_cov k 0x143000 0x144000
          && cells_ok k
          && (Z.eqb w (apf_buf T) || Z.eqb w (apf_buf T + 2) || Z.eqb w (apf_buf T + 4))
          && Z.leb 0 (apf_buf T) && Z.ltb (apf_buf T + 1024) two64
          && kzero_lit k APF_FMT_SHW (APF_FMT_SHW + 8)
          && kzero_lit k (APF_SB + apf_buf T / 8 - 8) (APF_SB + (apf_buf T + 1024) / 8 + 8)
          && kzero_lit k (APF_SB + splo / 8 - APF_WIN / 8 - 8) (APF_SB + sphi / 8 + 8))%bool
      then
        let k4 := kn_havocs k [(qb, qk, ELit APF_WIN); (ELit 0, apf_file T, ELit 4); (ELit 0, apf_file T + 40, ELit 8); (ELit 0, w, ELit 2)] in
        after_call nx0 cs ret None
          (KWord (SA (ELit 0) (apf_file T)) 4 (ELit 5) :: KWord (SA (ELit 0) (apf_file T + 40)) 8 (ELit (w + 2))
           :: KWord (SA (ELit 0) w) 2 (ELit 0x0a30) :: k4)
      else None
    | _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition first_false (i : nat) (l : list bool) : nat :=
  (fix go (i : nat) (l : list bool) := match l with [] => 0%nat | b :: r => if b then go (S i) r else i end) i l.
Definition diag_printfd (cs : acs) : nat :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (apf_entry T)) then 100%nat else
  match ret_lit cs with
  | None => 101%nat
  | Some ret =>
    match cell_val8 k (apf_file T + 40) with
    | None => 102%nat
    | Some w =>
      let sp := reg cs 2 in
      let '(qb, qk) := split_lit (eaddz sp (- APF_WIN)) in
      match xlo k sp, xhi k sp with
      | Some splo, Some sphi =>
          first_false 1
            [is_zero k (reg cs 11); Z.leb 4 (ealign k sp); Z.leb (2 ^ 46) splo; Z.leb sphi 0x7fffffffffff;
             kwritable k k qb qk APF_WIN; flat_x k qb qk (ELit APF_WIN); fresh_ok nx0 cs;
             img_cov k 0x10000 0x4b000; img_cov k 0x143000 0x144000;
             lit_cellw k (apf_rvp T) 8 (apf_vp T); lit_cellw k (apf_rvfp T) 8 (apf_vfp T);          (* [comment removed for export] *)
             lit_cellw k (apf_rmc T) 8 (apf_mc T); lit_cellw k (apf_rms T) 8 (apf_ms T);            (* [comment removed for export] *)
             lit_cellw k (apf_init T) 1 1; lit_cellw k (apf_init T + 1) 1 1; lit_cellw k (apf_chkpf T) 1 1;   (* [comment removed for export] *)
             lit_cellw k (apf_sbc T) 8 APF_SB;                                                        (* [comment removed for export] *)
             lit_cellw k (apf_file T) 4 5; lit_cellw k (apf_file T + 32) 8 (apf_buf T + 1024);        (* [comment removed for export] *)
             lit_cellw k (apf_file T + 96) 8 1024;                                                    (* [comment removed for export] *)
             lit_cellw k (apf_file T + 140) 4 0xffffffff; lit_cellw k (apf_file T + 144) 4 0xffffffff;   (* [comment removed for export] *)
             cell_any8 k (apf_canc T);                                                                (* [comment removed for export] *)
             (Z.eqb w (apf_buf T) || Z.eqb w (apf_buf T + 2) || Z.eqb w (apf_buf T + 4));              (* [comment removed for export] *)
             Z.leb 0 (apf_buf T); Z.ltb (apf_buf T + 1024) two64;                                     (* [comment removed for export] *)
             kzero_lit k APF_FMT_SHW (APF_FMT_SHW + 8);                                               (* [comment removed for export] *)
             kzero_lit k (APF_SB + apf_buf T / 8 - 8) (APF_SB + (apf_buf T + 1024) / 8 + 8);           (* [comment removed for export] *)
             kzero_lit k (APF_SB + splo / 8 - APF_WIN / 8 - 8) (APF_SB + sphi / 8 + 8)]%bool            (* [comment removed for export] *)
      | _, _ => 103%nat
      end
    end
  end.

(* [comment removed for export] *)
Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 111 then node_printfd cs else None.
End WithSegs.
End WithFP1.

End PFN.
