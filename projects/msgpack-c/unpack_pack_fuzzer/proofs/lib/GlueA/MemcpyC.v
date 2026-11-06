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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC StrRegC GshC TolC.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MemcpyC.
Section WithSegs.
Variable segs : list Segment.

Fixpoint copy_bytes (fuel : nat) (i : int) (src dst : sv) (sofs dofs : int) (len : int) (st : sstate) : option sstate :=
  match fuel with
  | O => if PrimInt63.leb len i then Some st else None
  | S f =>
      if PrimInt63.leb len i then Some st else
      let w8 := PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land (PrimInt63.add sofs i) 7%uint63) 0%uint63
                && PrimInt63.eqb (PrimInt63.land (PrimInt63.add dofs i) 7%uint63) 0%uint63 in
      let w := if w8 then 8%uint63 else 1%uint63 in
      match do_load segs st (sv_alu ALU_ADD src (VL (wlit i))) w false with
      | inl (Some v) =>
          match do_store segs st (sv_alu ALU_ADD dst (VL (wlit i))) w v with
          | inl st' => copy_bytes f (PrimInt63.add i w) src dst sofs dofs len st'
          | inr _ => None
          end
      | _ =>

          match (if w8 then do_load segs st (sv_alu ALU_ADD src (VL (wlit i))) 1%uint63 false else inl None) with
          | inl (Some v1) =>
              match do_store segs st (sv_alu ALU_ADD dst (VL (wlit i))) 1%uint63 v1 with
              | inl st' => copy_bytes f (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
              | inr _ => None
              end
          | _ =>
              match TolC.skip_byte segs st (sv_alu ALU_ADD src (VL (wlit i))) (sv_alu ALU_ADD dst (VL (wlit i))) with
              | Some st' => copy_bytes f (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
              | None => None
              end
          end
      end
  end.

Definition in_region_s (fs : list fact) (r : region) (o : w64) (len : int) : bool :=
  RangeC.in_region r o len
  || (PrimInt63.eqb (rg_lo r) 0%uint63 && negb (wt o) && negb (wt (wadd o (wlit len))) && wleu o (wadd o (wlit len))
      && KnownT.KnownT.known_leu_t fs (VL (wadd o (wlit len))) (rg_hi r)).

Definition range_in (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) (needw : bool) : bool :=
  match IMap.find k (s_regs st) with
  | Some r => in_region_s (s_facts st) r o len && match RangeC.range_class segs st wl k o len needw with Some _ => true | None => false end
  | None => false
  end.

Definition disjoint_ok (ks kd : int) (os od : w64) (len : int) : bool :=
  if PrimInt63.eqb ks kd then Z.leb (w2Zs os + to_Z len) (w2Zs od) || Z.leb (w2Zs od + to_Z len) (w2Zs os) else true.

Definition src_ok (st : sstate) (wl : list (int * sv * w64)) (srcv : sv) (kd : int) (od : w64) (len : int) : option int :=
  match srcv with
  | VP ks os => if (if range_in st wl ks os len false then true else StrRegC.arg_range st wl ks os len)
                   && disjoint_ok ks kd os od len then Some (W64.wl os) else None
  | VL a => if RangeC.lit_low st a len || GshC.lit_gsh GshC.CFG_ASAN st a len then Some (W64.wl a) else None
  | _ => None
  end.

Definition copy_post (kd : int) (od : w64) (srcv : sv) (sofs : int) (len : int) (st2 : sstate) : option (list sstate) :=
  match copy_bytes (Z.to_nat (to_Z len) + 1) 0%uint63 srcv (VP kd od) sofs (W64.wl od) len st2 with
  | Some stn => Some [stn]
  | None => None
  end.

Definition amemcpy_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X12 with
      | VP kd od, VL n =>
          let len := W64.wl n in

          let lenc := if PrimInt63.eqb len 0%uint63 then 1%uint63 else len in
          match src_ok st wl (getr st X11) kd od lenc with
          | Some sofs =>
              if negb (wt n) && PrimInt63.leb len RangeC.NMAX && range_in st wl kd od lenc true
              then copy_post kd od (getr st X11) sofs len (setpc (setr (clobber st1) X10 (VP kd od)) r)
              else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition amemcpy_c (pc : int) : contract := Contract pc amemcpy_apply.
End WithSegs.
End MemcpyC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import RangeC.TwinB StrRegC.TwinB GshC.TwinB TolC.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MemcpyC.
Section WithSegs.
Variable segs : list Segment.

Fixpoint copy_bytes (fuel : nat) (i : int) (src dst : sv) (sofs dofs : int) (len : int) (st : sstate) : option sstate :=
  match fuel with
  | O => if PrimInt63.leb len i then Some st else None
  | S f =>
      if PrimInt63.leb len i then Some st else
      let w8 := PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land (PrimInt63.add sofs i) 7%uint63) 0%uint63
                && PrimInt63.eqb (PrimInt63.land (PrimInt63.add dofs i) 7%uint63) 0%uint63 in
      let w := if w8 then 8%uint63 else 1%uint63 in
      match do_load segs st (sv_alu ALU_ADD src (VL (wlit i))) w false with
      | inl (Some v) =>
          match do_store segs st (sv_alu ALU_ADD dst (VL (wlit i))) w v with
          | inl st' => copy_bytes f (PrimInt63.add i w) src dst sofs dofs len st'
          | inr _ => None
          end
      | _ =>

          match (if w8 then do_load segs st (sv_alu ALU_ADD src (VL (wlit i))) 1%uint63 false else inl None) with
          | inl (Some v1) =>
              match do_store segs st (sv_alu ALU_ADD dst (VL (wlit i))) 1%uint63 v1 with
              | inl st' => copy_bytes f (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
              | inr _ => None
              end
          | _ =>
              match TolC.TwinB.TolC.skip_byte segs st (sv_alu ALU_ADD src (VL (wlit i))) (sv_alu ALU_ADD dst (VL (wlit i))) with
              | Some st' => copy_bytes f (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
              | None => None
              end
          end
      end
  end.

Definition in_region_s (fs : list fact) (r : region) (o : w64) (len : int) : bool :=
  RangeC.TwinB.RangeC.in_region r o len
  || (PrimInt63.eqb (rg_lo r) 0%uint63 && negb (wt o) && negb (wt (wadd o (wlit len))) && wleu o (wadd o (wlit len))
      && KnownT.KnownT.known_leu_t fs (VL (wadd o (wlit len))) (rg_hi r)).

Definition range_in (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) (needw : bool) : bool :=
  match IMap.find k (s_regs st) with
  | Some r => in_region_s (s_facts st) r o len && match RangeC.TwinB.RangeC.range_class segs st wl k o len needw with Some _ => true | None => false end
  | None => false
  end.

Definition disjoint_ok (ks kd : int) (os od : w64) (len : int) : bool :=
  if PrimInt63.eqb ks kd then Z.leb (w2Zs os + to_Z len) (w2Zs od) || Z.leb (w2Zs od + to_Z len) (w2Zs os) else true.

Definition src_ok (st : sstate) (wl : list (int * sv * w64)) (srcv : sv) (kd : int) (od : w64) (len : int) : option int :=
  match srcv with
  | VP ks os => if (if range_in st wl ks os len false then true else StrRegC.TwinB.StrRegC.arg_range st wl ks os len)
                   && disjoint_ok ks kd os od len then Some (W64.wl os) else None
  | VL a => if RangeC.TwinB.RangeC.lit_low st a len || GshC.TwinB.GshC.lit_gsh GshC.TwinB.GshC.CFG_ASAN st a len then Some (W64.wl a) else None
  | _ => None
  end.

Definition copy_post (kd : int) (od : w64) (srcv : sv) (sofs : int) (len : int) (st2 : sstate) : option (list sstate) :=
  match copy_bytes (Z.to_nat (to_Z len) + 1) 0%uint63 srcv (VP kd od) sofs (W64.wl od) len st2 with
  | Some stn => Some [stn]
  | None => None
  end.

Definition amemcpy_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X12 with
      | VP kd od, VL n =>
          let len := W64.wl n in

          let lenc := if PrimInt63.eqb len 0%uint63 then 1%uint63 else len in
          match src_ok st wl (getr st X11) kd od lenc with
          | Some sofs =>
              if negb (wt n) && PrimInt63.leb len RangeC.TwinB.RangeC.NMAX && range_in st wl kd od lenc true
              then copy_post kd od (getr st X11) sofs len (setpc (setr (clobber st1) X10 (VP kd od)) r)
              else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition amemcpy_c (pc : int) : contract := Contract pc amemcpy_apply.
End WithSegs.
End MemcpyC.
End TwinB.
