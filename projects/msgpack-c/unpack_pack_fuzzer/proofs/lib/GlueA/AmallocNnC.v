(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module AmallocNnC.

Definition PRIST_LO : sv := VL ActrA.PRIST_BASEw.

Fixpoint del_win3 (n : nat) (ws : list sv) (lo sz kd0 : sv) : option (list sv) :=
  match n, ws with
  | S n', l :: s :: kd :: ws' =>
      if sv_eqb l lo && sv_eqb s sz && sv_eqb kd kd0 then Some ws'
      else match del_win3 n' ws' lo sz kd0 with Some ws'' => Some (l :: s :: kd :: ws'') | None => None end
  | _, _ => None
  end.
Definition heap_del_prist (args : list sv) : option (list sv) :=
  match heap_nwin args, args with
  | Some n, VL md :: a :: VL nw :: rest =>
      match del_win3 n (firstn (3 * n) rest) PRIST_LO (VL wzero) (VL wzero) with
      | Some ws => Some (VL md :: a :: VL (wsub nw wone) :: ws ++ skipn (3 * n) rest)
      | None => None
      end
  | _, _ => None
  end.
Definition has_prist (hargs : list sv) : bool := match heap_del_prist hargs with Some _ => true | None => false end.

Definition del_prist (st : sstate) : sstate :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_del_prist hargs with
      | Some h' => set_ops st (set_op HEAP_ID h' (s_ops st))
      | None => st
      end
  | None => st
  end.

Definition SEC_MINw : w64 := wlit 64512%uint63.
Definition SEC_MAXw : w64 := wlit 268435456%uint63.
Definition CRED_LOWw : w64 := wlit 50465865728%uint63.

Definition arm_sec (fs : list fact) (n cred : sv) : bool :=
  known_ltu fs (VL SEC_MINw) n && known_leu fs n (VL SEC_MAXw) && known_leu fs (VL CRED_LOWw) cred.
Definition arm_prim (fs : list fact) (n : sv) (hargs : list sv) : bool := ActrA.prim_decided fs n && has_prist hargs.

Definition amalloc_nn_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_A hargs with
      | Some cred =>
          let fs := s_facts st in let n := getr st X10 in
          if arm_sec fs n cred then
            match ActrA.amalloc_apply UNIV PCz st with Some (stN :: posts) => Some posts | _ => None end
          else if arm_prim fs n hargs then
            match ActrA.amalloc_apply UNIV PCz (del_prist st) with Some (stN :: posts) => Some posts | _ => None end
          else None
      | None => None
      end
  | None => None
  end.
Definition amalloc_nn_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (amalloc_nn_apply UNIV PCz).

Definition prist_drop_apply (st : sstate) : option (list sstate) := Some [del_prist st].
Definition prist_drop_c (pc : int) : contract := Contract pc prist_drop_apply.
End AmallocNnC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import Actr.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module AmallocNnC.

Definition PRIST_LO : sv := VL ActrA.PRIST_BASEw.

Fixpoint del_win3 (n : nat) (ws : list sv) (lo sz kd0 : sv) : option (list sv) :=
  match n, ws with
  | S n', l :: s :: kd :: ws' =>
      if sv_eqb l lo && sv_eqb s sz && sv_eqb kd kd0 then Some ws'
      else match del_win3 n' ws' lo sz kd0 with Some ws'' => Some (l :: s :: kd :: ws'') | None => None end
  | _, _ => None
  end.
Definition heap_del_prist (args : list sv) : option (list sv) :=
  match heap_nwin args, args with
  | Some n, VL md :: a :: VL nw :: rest =>
      match del_win3 n (firstn (3 * n) rest) PRIST_LO (VL wzero) (VL wzero) with
      | Some ws => Some (VL md :: a :: VL (wsub nw wone) :: ws ++ skipn (3 * n) rest)
      | None => None
      end
  | _, _ => None
  end.
Definition has_prist (hargs : list sv) : bool := match heap_del_prist hargs with Some _ => true | None => false end.

Definition del_prist (st : sstate) : sstate :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_del_prist hargs with
      | Some h' => set_ops st (set_op HEAP_ID h' (s_ops st))
      | None => st
      end
  | None => st
  end.

Definition SEC_MINw : w64 := wlit 64512%uint63.
Definition SEC_MAXw : w64 := wlit 268435456%uint63.
Definition CRED_LOWw : w64 := wlit 50465865728%uint63.

Definition arm_sec (fs : list fact) (n cred : sv) : bool :=
  known_ltu fs (VL SEC_MINw) n && known_leu fs n (VL SEC_MAXw) && known_leu fs (VL CRED_LOWw) cred.
Definition arm_prim (fs : list fact) (n : sv) (hargs : list sv) : bool := ActrA.prim_decided fs n && has_prist hargs.

Definition amalloc_nn_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_A hargs with
      | Some cred =>
          let fs := s_facts st in let n := getr st X10 in
          if arm_sec fs n cred then
            match ActrA.amalloc_apply UNIV PCz st with Some (stN :: posts) => Some posts | _ => None end
          else if arm_prim fs n hargs then
            match ActrA.amalloc_apply UNIV PCz (del_prist st) with Some (stN :: posts) => Some posts | _ => None end
          else None
      | None => None
      end
  | None => None
  end.
Definition amalloc_nn_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (amalloc_nn_apply UNIV PCz).

Definition prist_drop_apply (st : sstate) : option (list sstate) := Some [del_prist st].
Definition prist_drop_c (pc : int) : contract := Contract pc prist_drop_apply.
End AmallocNnC.
End TwinB.
