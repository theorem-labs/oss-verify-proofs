(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step.
Open Scope Z_scope.
Unset Lia Cache.

Module TolC.
Section WithSegs.
Variable segs : list Segment.

Definition region_unk1 (r : region) (o : int) : region :=
  let g := granule o in let i := gidx o in
  let '(dirty, s) := match IMap.find g (rg_cells r) with Some (Gran d s) => (d, s) | None => (false, []) end in
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.add g (Gran true (cut s i 1%uint63)) (rg_cells r)).

Definition is_block_bg (b : bg) : bool := match b with BGNone | BGUnk => true | _ => false end.

Definition src_byte_ok (st : sstate) (a : sv) : bool :=
  match addr_of a with
  | Some (k, o) =>
      match IMap.find k (s_regs st), okey o with
      | Some r, Some key => can_read segs (s_facts st) (s_priv st) k r key 1%uint63
      | _, _ => false
      end
  | None => false
  end.

Definition forget_byte (st : sstate) (a : sv) : option sstate :=
  match addr_of a with
  | Some (k, o) =>
      match IMap.find k (s_regs st), okey o with
      | Some r, Some key =>
          if is_block_bg (rg_bg r) && can_write segs (s_facts st) (s_priv st) k r key 1%uint63
          then Some (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add k (region_unk1 r key) (s_regs st))
                        (s_facts st) (s_ops st) (s_priv st) (s_next st))
          else None
      | _, _ => None
      end
  | None => None
  end.

Definition skip_byte (st : sstate) (asrc adst : sv) : option sstate :=
  if src_byte_ok st asrc then forget_byte st adst else None.
End WithSegs.
End TolC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step.
Open Scope Z_scope.
Unset Lia Cache.

Module TolC.
Section WithSegs.
Variable segs : list Segment.

Definition region_unk1 (r : region) (o : int) : region :=
  let g := granule o in let i := gidx o in
  let '(dirty, s) := match IMap.find g (rg_cells r) with Some (Gran d s) => (d, s) | None => (false, []) end in
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.add g (Gran true (cut s i 1%uint63)) (rg_cells r)).

Definition is_block_bg (b : bg) : bool := match b with BGNone | BGUnk => true | _ => false end.

Definition src_byte_ok (st : sstate) (a : sv) : bool :=
  match addr_of a with
  | Some (k, o) =>
      match IMap.find k (s_regs st), okey o with
      | Some r, Some key => can_read segs (s_facts st) (s_priv st) k r key 1%uint63
      | _, _ => false
      end
  | None => false
  end.

Definition forget_byte (st : sstate) (a : sv) : option sstate :=
  match addr_of a with
  | Some (k, o) =>
      match IMap.find k (s_regs st), okey o with
      | Some r, Some key =>
          if is_block_bg (rg_bg r) && can_write segs (s_facts st) (s_priv st) k r key 1%uint63
          then Some (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add k (region_unk1 r key) (s_regs st))
                        (s_facts st) (s_ops st) (s_priv st) (s_next st))
          else None
      | _, _ => None
      end
  | None => None
  end.

Definition skip_byte (st : sstate) (asrc adst : sv) : option sstate :=
  if src_byte_ok st asrc then forget_byte st adst else None.
End WithSegs.
End TolC.
End TwinB.
