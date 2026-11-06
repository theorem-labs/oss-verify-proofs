(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore DepotIntro.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module XDP.

Definition DEP_D : Z := 0x189898.     (* [comment removed for export] *)
Definition DEP_SS : Z := 0x179888.    (* [comment removed for export] *)
Definition PUT_PC : Z := 0x71f34.     (* [comment removed for export] *)
Definition ACEILZ : Z := 0x7fff7f800000.
Definition ROD_LO : Z := 0x10000.
Definition ROD_HI : Z := 0x30000.
Definition DEPOT_ID : nat := 112.     (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint find_dinv (k : list kentry) : option (Z * expr * expr) :=
  match k with
  | [] => None
  | KInv O [ELit d; ELit ss; ELit kk; b17; b18] :: r =>
      if (Z.eqb d DEP_D && Z.eqb ss DEP_SS)%bool then Some (kk, b17, b18) else find_dinv r
  | _ :: r => find_dinv r
  end.

(* [comment removed for export] *)
Definition has_rodata (k : list kentry) : bool :=
  existsb (fun K => match K with KImg lo hi => (Z.leb lo ROD_LO && Z.leb ROD_HI hi)%bool | _ => false end) k.

Section Put.
Variable nx0 : nat.

Definition node_put (cs : acs) : option acs :=
  let k := kn cs in let bc := AX2B.mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) PUT_PC) then None else
  match find_dinv k, ret_lit cs with
  | Some (K, b17, b18), Some ret =>
      let sp := reg cs 2 in let tr := reg cs 10 in let s := reg cs 11 in
      let '(sb, sk) := split_lit sp in let '(tb, tk) := split_lit tr in
      match AX2B.xloB bc sp, AX2B.xhiB bc sp, AX2B.xloB bc tr, AX2B.xhiB bc tr, AX2B.xloB bc s, AX2B.xhiB bc s with
      | Some splo, Some sphi, Some trlo, Some trhi, Some slo, Some shi =>
          if (Z.leb 1 K && Z.ltb K 65535 && Z.leb ACEILZ (splo - 272) && Z.leb sphi (2 ^ 47)
              && Z.leb ACEILZ trlo && Z.leb (trhi + 16) (2 ^ 47) && Z.leb 1 slo && Z.leb shi 2
              && Z.leb 4 (AX2B.ealignB bc sp) && Z.leb 3 (AX2B.ealignB bc tr)
              && kwritable_xB bc k sb (sk - 272) (ELit 272) && kwritable_xB bc k tb tk (ELit 16)
              && AX2B.ranges_apart_xB bc tb tk (ELit 16) sb (sk - 272) (ELit 272)
              && AX2B.ranges_apart_xB bc b17 0 (ELit 1048576) sb (sk - 272) (ELit 272)
              && AX2B.ranges_apart_xB bc b18 0 (ELit 4096) sb (sk - 272) (ELit 272)
              && AX2B.ranges_apart_xB bc b17 0 (ELit 1048576) tb tk (ELit 16)
              && AX2B.ranges_apart_xB bc b18 0 (ELit 4096) tb tk (ELit 16)
              && has_rodata k)%bool
          then
            let k1 := kn_havocM k sb (sk - 272) (ELit 272) in
            let k2 := kn_havocM k1 (ELit 0) DEP_SS (ELit 32) in
            let k3 := kn_havocM k2 (ELit 0) DEP_D (ELit 0x400018) in
            let k4 := kn_havocM k3 b17 0 (ELit 1048576) in
            let k5 := kn_havocM k4 b18 0 (ELit 4096) in
            after_call nx0 cs ret None (KInv O [ELit DEP_D; ELit DEP_SS; ELit (K - 1); b17; b18] :: k5)
          else None
      | _, _, _, _, _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition xn (args : list expr) (cs : acs) : option acs :=
  match args with [] => node_put cs | _ => None end.
End Put.

(* [comment removed for export] *)
Definition DEPOT_INTRO_ID : nat := 113.   (* [comment removed for export] *)
Definition node_intro (segs : list Segment) (K : Z) (cs : acs) : option acs :=
  let k := kn cs in
  match DIN.kreadE segs k (ELit 0) (DEP_D + 0x400010) 8, DIN.kreadE segs k (ELit 0) (DEP_SS + 16) 8 with
  | Some e17, Some e18 =>
      if DIN.depot_intro_chk segs DEP_D DEP_SS K k
      then Some (set_kn cs (KInv O [ELit DEP_D; ELit DEP_SS; ELit K; e17; e18] :: k)) else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition xn_intro (segs : list Segment) (args : list expr) (cs : acs) : option acs :=
  match args with [ELit K] => node_intro segs K cs | _ => None end.

End XDP.
