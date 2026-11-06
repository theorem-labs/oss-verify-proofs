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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC StrRegC MemcpyC PubC GshC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module MemcpyPC.
Section WithSegs.
Variable segs : list Segment.

Definition src_ok_p (st : sstate) (wl : list (int * sv * w64)) (srcv : sv) (len : int) : option int :=
  match srcv with
  | VP ks os => if (if MemcpyC.range_in segs st wl ks os len false then true else StrRegC.arg_range st wl ks os len) then Some (W64.wl os) else None
  | VL a => if RangeC.lit_low st a len || GshC.lit_gsh GshC.CFG_ASAN st a len then Some (W64.wl a) else None
  | _ => None
  end.

Definition copy_post_p (a : w64) (srcv : sv) (sofs : int) (len : int) (st2 : sstate) : option (list sstate) :=
  match MemcpyC.copy_bytes segs (Z.to_nat (to_Z len) + 1) 0%uint63 srcv (VL a) sofs (W64.wl a) len st2 with
  | Some stn => Some [stn]
  | None => None
  end.

Definition amemcpyp_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X12 with
      | VL a, VL n =>
          let len := W64.wl n in
          let lenc := if PrimInt63.eqb len 0%uint63 then 1%uint63 else len in
          match src_ok_p st wl (getr st X11) lenc with
          | Some sofs =>
              if negb (wt n) && PrimInt63.leb len RangeC.NMAX && PubC.lit_pub st a lenc
              then copy_post_p a (getr st X11) sofs len (setpc (setr (clobber st1) X10 (VL a)) r)
              else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition amemcpyp_c (pc : int) : contract := Contract pc amemcpyp_apply.
End WithSegs.
End MemcpyPC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import RangeC.TwinB StrRegC.TwinB MemcpyC.TwinB PubC.TwinB GshC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module MemcpyPC.
Section WithSegs.
Variable segs : list Segment.

Definition src_ok_p (st : sstate) (wl : list (int * sv * w64)) (srcv : sv) (len : int) : option int :=
  match srcv with
  | VP ks os => if (if MemcpyC.TwinB.MemcpyC.range_in segs st wl ks os len false then true else StrRegC.TwinB.StrRegC.arg_range st wl ks os len) then Some (W64.wl os) else None
  | VL a => if RangeC.TwinB.RangeC.lit_low st a len || GshC.TwinB.GshC.lit_gsh GshC.TwinB.GshC.CFG_ASAN st a len then Some (W64.wl a) else None
  | _ => None
  end.

Definition copy_post_p (a : w64) (srcv : sv) (sofs : int) (len : int) (st2 : sstate) : option (list sstate) :=
  match MemcpyC.TwinB.MemcpyC.copy_bytes segs (Z.to_nat (to_Z len) + 1) 0%uint63 srcv (VL a) sofs (W64.wl a) len st2 with
  | Some stn => Some [stn]
  | None => None
  end.

Definition amemcpyp_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X12 with
      | VL a, VL n =>
          let len := W64.wl n in
          let lenc := if PrimInt63.eqb len 0%uint63 then 1%uint63 else len in
          match src_ok_p st wl (getr st X11) lenc with
          | Some sofs =>
              if negb (wt n) && PrimInt63.leb len RangeC.TwinB.RangeC.NMAX && PubC.TwinB.PubC.lit_pub st a lenc
              then copy_post_p a (getr st X11) sofs len (setpc (setr (clobber st1) X10 (VL a)) r)
              else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition amemcpyp_c (pc : int) : contract := Contract pc amemcpyp_apply.
End WithSegs.
End MemcpyPC.
End TwinB.
