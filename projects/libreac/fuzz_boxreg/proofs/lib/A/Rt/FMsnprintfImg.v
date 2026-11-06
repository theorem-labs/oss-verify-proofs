(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/ACf0.v, with its module paths changed; 45 of its 65 lines of code are new or changed and 59 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMsnprintfImg.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan: module paths changed; 31 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: FMupoison -> lib.A.Rt. *)
(* fm.asan's snprintf chain, image constants without any stack window: the code and return addresses the walks name,
   and the memcpy / memset interceptor contract aintrin_realizesU. Split out of FMsnprintfI.v and FMsnprintfGI.v (which
   re-export this file) so that the shared-contract chain does not reach their stack bands. New file. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fm.asan addresses ---- *)
Definition A_SNI : Z := 0x452c0.    (* __interceptor_snprintf *)
Definition A_VSNI : Z := 0x44ed0.   (* __interceptor_vsnprintf *)
Definition A_PCOM : Z := 0x44354.   (* printf_common (ctx, format, aq) *)
Definition A_VFPI : Z := 0x44e1c.   (* __interceptor_vfprintf *)
Definition A_VSN : Z := 0x91aec.    (* musl vsnprintf *)
Definition A_VFP : Z := 0x8e9c0.    (* musl vfprintf *)
Definition A_PCORE : Z := 0x8eb70.  (* musl printf_core *)
Definition A_FWX : Z := 0x8e600.    (* musl __fwritex *)
Definition A_SNW : Z := 0x91bb8.    (* musl sn_write *)
Definition W_MEMCPY : Z := 0x51094. (* __wrap_memcpy *)
Definition W_MEMSET : Z := 0x51090. (* __wrap_memset *)
Definition W_STRNLEN : Z := 0x413f0. (* __wrap_strnlen *)
Definition W_VFPRINTF : Z := 0x41424.
Definition RA_PCORE0 : Z := 0x8ea28. (* vfprintf's return points: printf_core (0, ..) *)
Definition RA_PCORE : Z := 0x8eac8. (* printf_core (f, ..) *)
Definition RA_FLUSH : Z := 0x8eae8. (* f->write (f, 0, 0) *)

(* ---- fm.asan addresses of the glue above printf_core (from FMsnprintfGI.v) ---- *)
Definition A_TRY : Z := 0x590a8.        (* __asan::TryAsanInitFromRtl *)
Definition RA_VSNI : Z := 0x45318.      (* __interceptor_snprintf: return from the vsnprintf interceptor *)
Definition RA_PCOM_VSNI : Z := 0x44f48. (* __interceptor_vsnprintf: return from printf_common *)
Definition RA_VSN : Z := 0x44f64.       (* __interceptor_vsnprintf: return from REAL (vsnprintf) *)
Definition WRC_ENTRY : Z := 0x45048.    (* __interceptor_vsnprintf: WRITE_RANGE (str, res + 1), size >= res + 1 *)
Definition WRC_END : Z := 0x44fcc.
Definition RA_MSET : Z := 0x91b50.      (* musl vsnprintf: return from memset *)
Definition RA_VFPI : Z := 0x91b8c.      (* musl vsnprintf: return from __wrap_vfprintf *)
Definition RA_PCOM_VFPI : Z := 0x44e74. (* __interceptor_vfprintf: return from printf_common *)
Definition RA_VFP : Z := 0x44e8c.       (* __interceptor_vfprintf: return from REAL (vfprintf) *)
Definition SLOT_VSN : Z := 0x9ac28.     (* REAL (vsnprintf) = A_VSN *)
Definition SLOT_VFP : Z := 0x9ac20.     (* REAL (vfprintf) = A_VFP *)
Definition SLOT_CFLAGS : Z := 0x98ea8.  (* -> common_flags 0x1338a8; check_printf at + 0x54 *)
Definition A_CHECK_PRINTF : Z := 0x132afc.
Definition A_ASAN_INITED : Z := 0xa1c58.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
#[local] Abbreviation segs := tfibsegs.
(* memcpy (OCpy) / memset (OSet) interceptor, as YG0d.v aintrin_realizes with ARU in and out. *)
Definition aintrin_realizesU (op : memop) (pc : Z) : Prop :=
forall ly S U W regs mem md d x n,
ecall_preU segs B ly S U W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok segs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
| OSet => True end) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End i.
