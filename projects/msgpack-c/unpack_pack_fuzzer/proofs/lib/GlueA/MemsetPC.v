(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC MemsetC PubC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module MemsetPC.
Section WithSegs.
Variable segs : list Segment.

Definition set_bytes_post_p (a : w64) (b len : int) (st2 : sstate) : option (list sstate) :=
  match MemsetC.set_bytes segs (Z.to_nat (to_Z len) + 1) 0%uint63 (VL a) (W64.wl a) b len st2 with
  | Some stn => Some [stn]
  | None => None
  end.

Definition amemsetp_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X11, getr st X12 with
      | VL a, VL c, VL n =>
          let len := W64.wl n in let b := PrimInt63.land (W64.wl c) 255%uint63 in
          if negb (wt n) && PrimInt63.leb 1%uint63 len && PrimInt63.leb len MemsetC.NMAX && PubC.lit_pub st a len
          then set_bytes_post_p a b len (setpc (setr (clobber st1) X10 (VL a)) r)
          else None
      | _, _, _ => None
      end
  | None => None
  end.

Definition amemsetp_c (pc : int) : contract := Contract pc amemsetp_apply.
End WithSegs.
End MemsetPC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import RangeC.TwinB MemsetC.TwinB PubC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module MemsetPC.
Section WithSegs.
Variable segs : list Segment.

Definition set_bytes_post_p (a : w64) (b len : int) (st2 : sstate) : option (list sstate) :=
  match MemsetC.TwinB.MemsetC.set_bytes segs (Z.to_nat (to_Z len) + 1) 0%uint63 (VL a) (W64.wl a) b len st2 with
  | Some stn => Some [stn]
  | None => None
  end.

Definition amemsetp_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X11, getr st X12 with
      | VL a, VL c, VL n =>
          let len := W64.wl n in let b := PrimInt63.land (W64.wl c) 255%uint63 in
          if negb (wt n) && PrimInt63.leb 1%uint63 len && PrimInt63.leb len MemsetC.TwinB.MemsetC.NMAX && PubC.TwinB.PubC.lit_pub st a len
          then set_bytes_post_p a b len (setpc (setr (clobber st1) X10 (VL a)) r)
          else None
      | _, _, _ => None
      end
  | None => None
  end.

Definition amemsetp_c (pc : int) : contract := Contract pc amemsetp_apply.
End WithSegs.
End MemsetPC.
End TwinB.
