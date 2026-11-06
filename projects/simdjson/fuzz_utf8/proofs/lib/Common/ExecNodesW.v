(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ExecNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module EXW.

Definition two31 : Z := 2 ^ 31.
Definition two32 : Z := 2 ^ 32.
Definition negband_lo : Z := two64 - two31.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sx32b (e : expr) : bool :=
  match e with
  | EAluw _ _ _ => true
  | EMdw _ _ _ => true
  | EExt true _ n _ => (Nat.leb 1 n && Nat.leb n 4)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition band_clamp (lo hi : Z) : Z * Z :=
  ((if Z.ltb lo two31 then lo else Z.max lo negband_lo),
   (if Z.leb negband_lo hi then hi else Z.min hi (two31 - 1))).

Definition reg_ix (r : Z) : option nat :=
  let rn := Z.to_nat r in if (Nat.ltb 0 rn && Nat.ltb rn 32)%bool then Some rn else None.

(* [comment removed for export] *)
Definition node_sxband (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit r] =>
      match reg_ix r with
      | Some rn =>
          let e := reg cs rn in
          if sx32b e then
            match erange (kn cs) e with
            | Some (lo, hi) => let '(lo', hi') := band_clamp lo hi in Some (set_kn cs (KRange e lo' hi' :: kn cs))
            | None => None
            end
          else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition sband (r : option (Z * Z)) : option (Z * Z) :=
  match r with
  | Some (lo, hi) =>
      if (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two31)%bool then Some (lo, hi)
      else if (Z.leb negband_lo lo && Z.leb lo hi && Z.ltb hi two64)%bool then Some (lo - two64, hi - two64)
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition wq (s : Z) : Z := (s + two31) / two32.

(* [comment removed for export] *)
Definition node_wop64 (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit r] =>
      match reg_ix r with
      | Some rn =>
          match reg cs rn with
          | EAluw op a b =>
              match (match op with ALU_ADD => Some true | ALU_SUB => Some false | _ => None end) with
              | Some isadd =>
                  match sband (erange (kn cs) a), sband (erange (kn cs) b) with
                  | Some (al, ah), Some (bl, bh) =>
                      let rl := if isadd then al + bl else al - bh in
                      let rh := if isadd then ah + bh else ah - bl in
                      let q := wq rl in
                      if Z.eqb q (wq rh) then
                        let wl := rl - two32 * q in
                        let wh := rh - two32 * q in
                        let e' := if Z.eqb q 0 then mkAlu op a b else EAluw op a b in   (* [comment removed for export] *)
                        let facts := if Z.leb 0 wl then [KRange e' wl wh]
                                     else if Z.ltb wh 0 then [KRange e' (wl + two64) (wh + two64)]
                                     else [] in
                        Some (set_kn (set_reg cs rn e') (facts ++ kn cs))
                      else None
                  | _, _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_zeroword (cs : acs) (args : list expr) : option acs :=
  match args with
  | [a; ELit nz] =>
      let k := kn cs in
      let '(ab, ao) := split_lit a in
      if ((Z.eqb nz 1 || Z.eqb nz 2 || Z.eqb nz 4 || Z.eqb nz 8) && kzero_x k k ab ao (ELit nz))%bool
      then Some (set_kn cs (KWord (SA ab ao) (Z.to_nat nz) (ELit 0) :: k))
      else None
  | _ => None
  end.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable nx0 : nat.
(* [comment removed for export] *)
Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 46%nat => node_sxband cs args
  | 47%nat => node_wop64 cs args
  | 48%nat => node_zeroword cs args
  | _ => EXN.xn segs IT nx0 id args cs
  end.
End WithSegs.
End EXW.
