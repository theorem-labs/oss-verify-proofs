(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/ACf0.v, with its module paths changed; 45 of its 65 lines of code are new or changed and 59 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfImg.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 29 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Modified by Theorem Labs, 2026-10 (fuzz_command P8c, by hand): A_SNI 0x45c90 -> 0x49fb8 (___interceptor_snprintf) and W_MEMSET 0x51a60 -> 0x57628 (__wrap_memset = __interceptor_trampoline_memset), which the tool left (two names at each address); SLOT_CFLAGS's comment names our common_flags 0x142be8. *)
(* fm.asan's snprintf chain, image constants without any stack window: the code and return addresses the walks name,
   and the memcpy / memset interceptor contract aintrin_realizesU. Split out of FMsnprintfI.v and FMsnprintfGI.v (which
   re-export this file) so that the shared-contract chain does not reach their stack bands. New file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFupoison.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fm.asan addresses ---- *)
Definition A_SNI : Z := 0x49fb8.    (* __interceptor_snprintf *)
Definition A_VSNI : Z := 0x49858.   (* __interceptor_vsnprintf *)
Definition A_PCOM : Z := 0x48cdc.   (* printf_common (ctx, format, aq) *)
Definition A_VFPI : Z := 0x497a4.   (* __interceptor_vfprintf *)
Definition A_VSN : Z := 0x9e490.    (* musl vsnprintf *)
Definition A_VFP : Z := 0x9b364.    (* musl vfprintf *)
Definition A_PCORE : Z := 0x9b514.  (* musl printf_core *)
Definition A_FWX : Z := 0x9afa4.    (* musl __fwritex *)
Definition A_SNW : Z := 0x9e55c.    (* musl sn_write *)
Definition W_MEMCPY : Z := 0x5762c. (* __wrap_memcpy *)
Definition W_MEMSET : Z := 0x57628. (* __wrap_memset *)
Definition W_STRNLEN : Z := 0x45134. (* __wrap_strnlen *)
Definition W_VFPRINTF : Z := 0x45174.
Definition RA_PCORE0 : Z := 0x9b3cc. (* vfprintf's return points: printf_core (0, ..) *)
Definition RA_PCORE : Z := 0x9b46c. (* printf_core (f, ..) *)
Definition RA_FLUSH : Z := 0x9b48c. (* f->write (f, 0, 0) *)

(* ---- fm.asan addresses of the glue above printf_core (from FMsnprintfGI.v) ---- *)
Definition A_TRY : Z := 0x5f640.        (* __asan::TryAsanInitFromRtl *)
Definition RA_VSNI : Z := 0x4a010.      (* __interceptor_snprintf: return from the vsnprintf interceptor *)
Definition RA_PCOM_VSNI : Z := 0x498d0. (* __interceptor_vsnprintf: return from printf_common *)
Definition RA_VSN : Z := 0x498ec.       (* __interceptor_vsnprintf: return from REAL (vsnprintf) *)
Definition WRC_ENTRY : Z := 0x499d0.    (* __interceptor_vsnprintf: WRITE_RANGE (str, res + 1), size >= res + 1 *)
Definition WRC_END : Z := 0x49954.
Definition RA_MSET : Z := 0x9e4f4.      (* musl vsnprintf: return from memset *)
Definition RA_VFPI : Z := 0x9e530.      (* musl vsnprintf: return from __wrap_vfprintf *)
Definition RA_PCOM_VFPI : Z := 0x497fc. (* __interceptor_vfprintf: return from printf_common *)
Definition RA_VFP : Z := 0x49814.       (* __interceptor_vfprintf: return from REAL (vfprintf) *)
Definition SLOT_VSN : Z := 0xa8198.     (* REAL (vsnprintf) = A_VSN *)
Definition SLOT_VFP : Z := 0xa8190.     (* REAL (vfprintf) = A_VFP *)
Definition SLOT_CFLAGS : Z := 0xa63e0.  (* -> common_flags 0x142be8; check_printf at + 0x54 *)
Definition A_CHECK_PRINTF : Z := 0x142c3c.
Definition A_ASAN_INITED : Z := 0xb1d98.

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
