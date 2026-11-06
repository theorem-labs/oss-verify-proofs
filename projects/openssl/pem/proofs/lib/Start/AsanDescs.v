(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Module DSC.

(* [comment removed for export] *)
Record dstat := DS { d_b0 : Z; d_b1 : Z; d_s0 : Z; d_s1 : Z; d_w0 : Z; d_w1 : Z; d_dy0 : Z; d_dy1 : Z; d_lo0 : Z; d_lo1 : Z;
                     d_t0 : Z; d_t1 : Z; d_p0 : Z; d_n0 : Z; d_n1 : Z; d_e0 : Z; d_e1 : Z; d_al : bool }.
Definition DBIG : Z := 2 ^ 64.
Definition ds0 : dstat := DS DBIG 0 DBIG 0 DBIG 0 DBIG 0 DBIG 0 DBIG 0 DBIG DBIG 0 DBIG 0 true.

Definition ds_add (s : dstat) (b sz w dy lo od : Z) : dstat :=
  let nn := w / 8 - sz / 8 in
  let t := (od + 1) mod DBIG in
  DS (Z.min (d_b0 s) b) (Z.max (d_b1 s) b) (Z.min (d_s0 s) sz) (Z.max (d_s1 s) sz) (Z.min (d_w0 s) w) (Z.max (d_w1 s) w)
     (Z.min (d_dy0 s) dy) (Z.max (d_dy1 s) dy) (Z.min (d_lo0 s) lo) (Z.max (d_lo1 s) lo)
     (Z.min (d_t0 s) t) (Z.max (d_t1 s) t) (if Z.leb 2 t then Z.min (d_p0 s) t else d_p0 s)
     (Z.min (d_n0 s) nn) (Z.max (d_n1 s) nn) (Z.min (d_e0 s) ((b + w) / 8)) (Z.max (d_e1 s) ((b + w) / 8))
     (d_al s && Z.eqb (b mod 32) 0 && Z.eqb (w mod 32) 0).

Section Descs.
Variable segs : list Segment.

Definition rd64 (a : Z) : option Z :=
  match img_bytes segs a 8 with Some bs => Some (zbytes_le_to_Z bs) | None => None end.

(* [comment removed for export] *)
Fixpoint dscan (n : nat) (a : Z) (s : dstat) : option dstat :=
  match n with
  | O => Some s
  | S n' =>
      match rd64 a, rd64 (a + 8), rd64 (a + 16), rd64 (a + 40), rd64 (a + 48), rd64 (a + 56) with
      | Some b, Some sz, Some w, Some dy, Some lo, Some od => dscan n' (a + 64) (ds_add s b sz w dy lo od)
      | _, _, _, _, _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition st_scan (tb n : Z) : option dstat := dscan (Z.to_nat n) tb ds0.
(* [comment removed for export] *)
Definition st_ok (ST : Z -> Z -> option dstat) : Prop := forall tb n s, ST tb n = Some s -> st_scan tb n = Some s.

(* [comment removed for export] *)
Definition descs_pre (nx0 : nat) (cs : acs) (tb n : Z) (J : nat) : bool :=
  (Z.leb 0 tb && Z.ltb (tb + 64 * n) (2 ^ 40) && Nat.ltb J (nxt cs) && img_cov (kn cs) tb (tb + 64 * n) && fresh_ok nx0 cs
   && match erange (kn cs) (EVar J) with Some (lo, hi) => Z.leb 0 lo && Z.ltb hi n | None => false end)%bool.

Definition stat_pre (s : dstat) : bool :=
  (d_al s && Z.eqb (d_dy0 s) (d_dy1 s) && Z.eqb (d_lo0 s) (d_lo1 s) && Z.leb 0 (d_n0 s)
   && Z.ltb (d_b1 s) (2 ^ 40) && Z.ltb (d_w1 s) (2 ^ 40) && Z.ltb (d_s1 s) (2 ^ 40))%bool.

(* [comment removed for export] *)
Definition node_descs (ST : Z -> Z -> option dstat) (nx0 : nat) (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit tb; ELit n; EVar J] =>
      let v := nxt cs in
      let base := escale 64 (EVar J) in
      if negb (descs_pre nx0 cs tb n J) then None else
      match ST tb n with
      | Some s =>
          if negb (stat_pre s) then None else
          let ebeg := escale 32 (EVar v) in let esz := eadd (escale 8 (EVar (S v))) (EVar (S (S (S v)))) in let eswr := escale 32 (EVar (S (S v))) in
          let kf := [KWord (SA base tb) 8 ebeg; KWord (SA base (tb + 8)) 8 esz; KWord (SA base (tb + 16)) 8 eswr;
                     KWord (SA base (tb + 40)) 8 (ELit (d_dy0 s)); KWord (SA base (tb + 48)) 8 (ELit (d_lo0 s))] in
          let kr := [KRange (EVar v) (d_b0 s / 32) (d_b1 s / 32); KRange (EVar (S v)) (d_s0 s / 8) (d_s1 s / 8);
                     KRange (EVar (S (S v))) (d_w0 s / 32) (d_w1 s / 32); KRange (EVar (S (S (S v)))) 0 7;
                     KRange (esub (escale 4 (EVar (S (S v)))) (EVar (S v))) (d_n0 s) (d_n1 s);
                     KRange (eadd (escale 4 (EVar v)) (escale 4 (EVar (S (S v))))) (d_e0 s) (d_e1 s)] in
          if Z.eqb (d_t0 s) (d_t1 s)
          then Some (bump (add_kn cs (kf ++ KWord (SA base (tb + 56)) 8 (ELit ((d_t0 s - 1) mod DBIG)) :: kr)) 4)
          else Some (bump (add_kn cs (kf ++ KWord (SA base (tb + 56)) 8 (eaddz (EVar (S (S (S (S v))))) (-1))
                                         :: KRange (EVar (S (S (S (S v))))) (d_t0 s) (d_t1 s) :: kr)) 5)
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_descs_refine (ST : Z -> Z -> option dstat) (nx0 : nat) (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit tb; ELit n; EVar J; EVar t] =>
      if negb (descs_pre nx0 cs tb n J) then None else
      match ST tb n, kread8e segs (kn cs) (escale 64 (EVar J)) (tb + 56), erange (kn cs) (EVar t) with
      | Some s, Some e, Some (lo, hi) =>
          if (expr_eqb e (eaddz (EVar t) (-1)) && Z.leb 2 lo)%bool
          then Some (add_kn cs [KRange (EVar t) (d_p0 s) (d_t1 s)])
          else None
      | _, _, _ => None
      end
  | _ => None
  end.

End Descs.
End DSC.
