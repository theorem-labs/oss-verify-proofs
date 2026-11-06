(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMH_Base.v and lib/A/FMH_Rt.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan: module paths changed; 3 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: fm lib.Reusable -> boxreg lib.Reusable, lib.A.FMupoison -> lib.A.Rt.FMupoison, FMH_Base's ecall_preU_k / cstr_ok / bytes_at / rom_viewN / rom_viewO -> lib.A.Rt.StrncmpFmh; FMPstat, ManifestModel not Required (no copied definition uses them). *)
(* Copied, names kept (fm file:line at 7e395de08f5): FMH_Base.v PC_snprintf :51, FM_GOT_canary :62, FM_canary :63, STK_RT_PRINTF :94, rdW :138 (local abbreviation), wdest_ok :186; FMH_Rt.v fpiece :38, fmt_bytes :39, FM_SN_FMTS :47, rdW :63 (local abbreviation), frender :68, asnprintf_realizes :181. Aliases of lib/A/Rt/StrncmpFmh.v (same text, not copied again): FMH_Base.v ecall_preU_k :162, cstr_ok :175, bytes_at :183, rom_viewN :218, rom_viewO :227. *)
(* libreac/fuzz_boxreg, build asan (fuzz_boxreg.asan eacfa20547ad): the file that carries the definitions of a Theorem Labs lane's
   FMH_Base.v and FMH_Rt.v that a Theorem Labs lane's relocated snprintf seam uses (the 18 lib/A/Rt/FMsnprintf*.v whose fm source
   at a working branch 7e395de08f5 Requires FMH_Base / FMH_Rt; RT_pf_shU.v also Requires FMH_Base
   but uses none of its names). Those fm files are NOT relocated: they Require fm's program model
   (lib/Prog/ManifestModel.v, lib/A/FMPstat.v); a Theorem Labs lane's 03:33Z ruling re-points their Requires to a boxreg file
   carrying the same definitions, as lib/A/Rt/StrncmpFmh.v does for the strncmp proof. In the relocated files the
   qualifiers FMH_Base. / FMH_Rt. become SnprintfFmh. FMPstat.v and ManifestModel.v give the seam nothing.
   - the names lib/A/Rt/StrncmpFmh.v already carries verbatim (ecall_preU_k, cstr_ok, bytes_at) or as aliases of
     StrncmpDef's identical bodies (rom_viewN, rom_viewO) are aliases of StrncmpFmh's here, not a second definition.
     StrncmpFmh is Required, not Imported, and the aliases name it qualified, so no StrncmpFmh name is shadowed here
     or in the files that import this one.
   - image A's values, each measured on the pin fuzz_boxreg.asan eacfa20547ad with its unstripped twin
     (the pinned fuzz_boxreg.asan, same sha256, + fuzz_boxreg.debug), keyed on symbol + offset
     (port_addr_check 5033540ba83b predict mode from fm.asan 0ba7e1695886; the format and the stack read off the image
     and boxreg's contracts):
     PC_snprintf = __interceptor_trampoline_snprintf+0x0 (fm 0x41314 -> 0x41430; boxreg's
       BS___interceptor_trampoline_snprintf, lib/A/Prog/BoxAddr.v:46);
     FM_GOT_canary = GOT[__stack_chk_guard+0x0], the one .got word that holds &__stack_chk_guard (fm 0x9a638 -> 0x99b40);
     FM_canary = __stack_chk_guard+0x0 (fm 0x5f4db0 -> 0x5f3f50); lib/A/Rt/SnprintfBridge.v:402-403 BOX_SNP_GC /
       BOX_SNP_GV hold the same two values;
     FM_SN_FMTS: fm's seven formats (FMT_whole .. FMT_t1x, FMH_Base.v:65-71, fm-only strings, no counterpart) become
       boxreg's one format "%s" = reac_boxreg.c's .str+0x0 (a 32-byte symbol of .rodata, a 3-byte registered global,
       bytes 25 73 00 then redzone), the listing's A_OBJ 10 (box_obj 10 = 0x20d40, lib/A/Prog/BoxAddr.v:60), the a2
       of both snprintf calls (lib/A/Rt/SnprintfDef.v:7-11);
     STK_RT_PRINTF = 2 * ESTACK = 8192, the window of boxreg's snprintf wrapper contract (lib/A/Rt/SnprintfDef.v
       asnprintf_realizes; amig's measure 8160 bytes, SnprintfDef.v:21-23) and the seam's K (0xa30 + 5552 <= 8192),
       not fm's 3 * ESTACK.
   No other image numeral. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI04 YI00 YK06 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require StrncmpFmh.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- FMH_Base names that are aliases of StrncmpFmh's (FMH_Base.v's text, verbatim there) ---- *)
Abbreviation ecall_preU_k := StrncmpFmh.ecall_preU_k (only parsing).
Abbreviation cstr_ok := StrncmpFmh.cstr_ok (only parsing).
Abbreviation bytes_at := StrncmpFmh.bytes_at (only parsing).
Abbreviation rom_viewN := StrncmpFmh.rom_viewN (only parsing).
Abbreviation rom_viewO := StrncmpFmh.rom_viewO (only parsing).

(* ---- FMH_Base.v, verbatim, image A's values ---- *)
(* runtime entries the target code calls (interceptor trampolines `__wrap_*`, musl isalnum, asan entry points) *)
Definition PC_snprintf : Z := 0x41430.
(* stack protector cells musl's printf_core reads (donor A/AE2d.v:35-36 A_GOT_canary / A_canary at cgif_file addresses):
   the .got slot and __stack_chk_guard *)
Definition FM_GOT_canary : Z := 0x99b40.
Definition FM_canary : Z := 0x5f3f50.
(* runtime calls: what each runtime contract (FMH_Rt.v) asks below the call's sp *)
Definition STK_RT_PRINTF : Z := 2 * ESTACK.   (* boxreg's snprintf wrapper contract: 8160 bytes (lib/A/Rt/SnprintfDef.v) *)

(* ---- FMH_Rt.v, verbatim, image A's format ---- *)
(* ---- snprintf formats: literal runs, %s, %.*s ---- *)
Inductive fpiece : Type := FLit (l : list Z) | FStr | FPStr.
Fixpoint fmt_bytes (ps : list fpiece) : list Z :=
  match ps with
  | [] => []
  | FLit l :: ps' => l ++ fmt_bytes ps'
  | FStr :: ps' => [37; 115] ++ fmt_bytes ps'
  | FPStr :: ps' => [37; 46; 42; 115] ++ fmt_bytes ps'
  end.
(* boxreg's one format and its pieces (MEASURED: "%s" and its NUL are the .rodata bytes at .str+0x0, A_OBJ 10) *)
Definition FM_SN_FMTS : list (Z * list fpiece) :=
  [(0x20d40, [FStr])].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- FMH_Base.v, verbatim ---- *)
Section c.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* a destination the walk may write n bytes at (donor dest_ok, YG0d.v:311, with an STK window) *)
Definition wdest_ok (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (d n : Z) : Prop :=
  0 <= d /\ d + n <= alloc_ceiling /\ amem_range d n /\
  (forall a, d <= a < d + n -> writable_at segs (rdW W mem) a /\ ~ aowned B ly S a /\ ~ (spZ regs - STK <= a < spZ regs)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n).
End c.
(* ---- FMH_Rt.v, verbatim ---- *)
Section c.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the output of the format pieces over the vararg register values (a3..a7); each %s / %.*s string a C string that does
   not overlap the destination [d, d + n); a %.*s precision is 1..len s, as fm uses it (fuzz_manifest.c:275-287:
   k in [1, n - 1]) *)
Fixpoint frender (W : world segs) (mem : word -> option byte) (d n : Z) (ps : list fpiece) (args : list Z)
  (out : list Z) : Prop :=
  match ps with
  | [] => out = []
  | FLit l :: ps' => exists out', out = l ++ out' /\ frender W mem d n ps' args out'
  | FStr :: ps' =>
      match args with
      | p :: args' => exists s out', cstr_ok segs W mem p s /\ (p + Z.of_nat (length s) + 1 <= d \/ d + n <= p) /\
          out = s ++ out' /\ frender W mem d n ps' args' out'
      | [] => False
      end
  | FPStr :: ps' =>
      match args with
      | k :: p :: args' => exists s out', 1 <= k <= Z.of_nat (length s) /\ cstr_ok segs W mem p s /\
          (p + Z.of_nat (length s) + 1 <= d \/ d + n <= p) /\
          out = firstn (Z.to_nat k) s ++ out' /\ frender W mem d n ps' args' out'
      | _ => False
      end
  end.

(* snprintf interceptor (__interceptor_trampoline_snprintf 0x41430 `j 0x452c0` -> ___interceptor_snprintf 0x452c0 ->
   vsnprintf interceptor ___interceptor_vsnprintf 0x44ed0: printf_common's %s checks, REAL = musl vsnprintf 0x91aec,
   then WRITE_RANGE (str, min (size, res + 1))) for boxreg's one format; the output fits; over ARU. The image facts
   musl's printf_core reads: rom_viewN (formats, word constants) and the stack-protector cells. *)
Definition asnprintf_realizes (pc : Z) : Prop :=
  forall ly S (U : list (Z * Z)) W regs mem md d sz f (ps : list fpiece) (out : list Z),
  ecall_preU_k segs B STK_RT_PRINTF ly S U W regs mem md -> rom_viewN segs B W mem ->
  (exists cval, val_mem segs (rdW W mem) FM_GOT_canary 8 FM_canary /\ val_mem segs (rdW W mem) FM_canary 8 cval /\
     0 <= cval < 2 ^ 64) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 sz -> getr regs 12 = w64 f ->
  In (f, ps) FM_SN_FMTS -> cstr_ok segs W mem f (fmt_bytes ps) ->
  frender W mem d sz ps (map (fun r : Z => bv_unsigned (getr regs (Z_to_bv 5 r))) [13; 14; 15; 16; 17]) out ->
  Z.of_nat (length out) + 1 <= sz <= 2 ^ 30 ->
  wdest_ok segs B STK_RT_PRINTF ly S W regs mem d (Z.of_nat (length out) + 1) ->
  (d + Z.of_nat (length out) + 1 <= FM_canary \/ FM_canary + 8 <= d) -> 0 < d ->
  (forall a, d <= a < d + Z.of_nat (length out) + 1 -> ~ in_rom segs a) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W (unpoison U mem') md' /\ upoisoned segs W mem' U /\
       aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (Z.of_nat (length out)) /\
       bytes_at segs W mem' d (out ++ [0]) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length out) + 1) ->
          ~ (spZ regs - STK_RT_PRINTF <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End b.
