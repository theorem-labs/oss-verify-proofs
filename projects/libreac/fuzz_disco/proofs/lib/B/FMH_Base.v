(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Base.v (a working branch 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan-ubsan by reloc.py (target disco-Y): module paths changed; 14 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan-ubsan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-Y.tsv); hand checks: FMPstat STOP: fm statics footprint; dropped with the FMH_Base subset (P8-*-base stop item); line 24 0x80b20 refused (predicted 0x837ec): fm check_no_overread+0x0: the target image has no symbol of that name; line 33 0x8193c refused (predicted 0x8467c): fm fuzz_malloc+0x0: the target image has no symbol of that name; line 45 0x412d4 refused (predicted 0x42a48): fm __interceptor_trampoline_strncmp+0x0: the target image has no symbol of that name; line 52 0x88350 refused (predicted 0x8f8d8): fm isalnum+0x0: the target image has no symbol of that name; line 57 0x5d4400 refused (predicted 0x5dbb00): fm g_live+0x0: the target image has no symbol of that name; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x20d40 at fm line 72: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x20d60 at fm line 66: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x20da0 at fm line 67: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x20de0 at fm line 68: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x20e40 at fm line 69: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x20ea0 at fm line 70: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x20f00 at fm line 71: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x20fa0 at fm line 65: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x412d4 at fm line 45: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x412d8 at fm line 46: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x412dc at fm line 47: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x80b20 at fm line 24: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x80db4 at fm line 25: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x80dd8 at fm line 26: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x80e14 at fm line 27: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x80e44 at fm line 28: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x80ea0 at fm line 29: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81130 at fm line 30: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81778 at fm line 31: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81880 at fm line 32: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x8193c at fm line 33: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81a78 at fm line 34: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81b94 at fm line 35: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81ba0 at fm line 36: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81bac at fm line 37: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81bc0 at fm line 38: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81be4 at fm line 39: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x81c04 at fm line 40: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x82130 at fm line 41: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x822c4 at fm line 42: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x88350 at fm line 52: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x9df80 at fm line 56: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x5d4420 at fm line 58: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it; provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv: 0x5d4440 at fm line 59: P0 status UNRESOLVED, decided DROP (provenance/evidence/g9-gxa/gates/numerals-rest.tsv): a hand removes it. *)
(* fm program part, statement base: fm.asan addresses, the per-function stack/event/live constants, the user-poison
   wrappers over the donor's afn_pre / apost_base, C-string premises, fm's static allocation counters (fuzz/alloc.c).
   Definitions only. *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane, G9 row P8-Y-base): the fuzz_disco.asan-ubsan twin. The tool line above
   relocated fm's whole file (exit 3 on the STOP module FMPstat, run with --allow-stop); by hand this file keeps only the
   SUBSET the G9 snprintf route reads (provenance/evidence/g9-gxa/g9tool/route-classes.tsv files FMbz_clean, FMrt_lift, FMrt_pre, FMsnprintfCr, FMsnprintfFm,
   FMsnprintfFmI, FMsnprintfGvsn0, FMsnprintfSeamI, FMsnprintfSnp, FMsnprintfSvsn, RT_pf_shU at fm 3e35620c52e):
   PC_snprintf, FM_GOT_canary, FM_canary, ecall_pre_k, ecall_preU_k, cstr, cstr_ok, bytes_at, rom_viewN, rom_viewO, each
   the tool's text. The three addresses are the tool's, checked against provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv, its A/FMH_Base.v rows for fm lines 51 / 62 / 63
   and the asan-ubsan .debug symtab (image sha256 cee6f04a): PC_snprintf = __interceptor_trampoline_snprintf =
   __wrap_snprintf (0x41314 -> 0x42a7c); FM_GOT_canary = the .got slot that __stdio_write+0x30, fmt_fp+0x60 and pad+0x20
   load (auipc/ld), holding &__stack_chk_guard (0x9a638 -> 0xa1538); FM_canary = __stack_chk_guard (0x5f4db0 ->
   0x5fc450). Removed Requires: lib.B.FMPstat (STOP; FMPstat.v is not copied), lib.Prog.ManifestModel and
   lib.Reusable.YC20 (absent in fuzz_disco). Dropped (fm harness, no route use, provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv HARNESS / UNRESOLVED):
   fm's other entries, targets and runtime PCs, the fuzz/alloc.c statics, fm's seven formats (disco's thirteen
   call-site formats, provenance/evidence/g9-gxa/gates/call-sites.tsv, are stated through SnFF's FF_disco, P2), the STK_ / EV_ / LIVE_ / CNT
   bounds, afn_preU, apost_baseU, wdest_ok, fm_glob, fm_stat, fm_rblock, stk_sh0, str_homeA. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fuzz_disco.asan-ubsan addresses (symbol + offset, provenance/evidence/g9-gxa/g9tool/p0-numerals.tsv) ---- *)
(* runtime entries the target code calls (interceptor trampolines `__wrap_*`) *)
Definition PC_snprintf : Z := 0x42a7c.
(* stack protector cells musl's printf_core reads (donor A/AE2d.v:35-36 A_GOT_canary / A_canary at cgif_file addresses):
   the .got slot and __stack_chk_guard *)
Definition FM_GOT_canary : Z := 0xa1538.
Definition FM_canary : Z := 0x5fc450.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ecall_pre (YG0d.v:277) with STK bytes of present stack, as abcmp_realizes asks (YG0d.v:355), and the stack above
   alloc_ceiling (astk_ok, YCbq.v:333), so a string below alloc_ceiling (cstr_ok) is outside the callee's window *)
Definition ecall_pre_k (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
  ecall_pre segs B ly S W regs mem md /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).

(* a Theorem Labs lane's ecall_preU (Rt/SnUpoison.v) with STK bytes of stack *)
Definition ecall_preU_k (STK : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ecall_preU segs B ly S U W regs mem md /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).

(* ---- C strings ---- *)
(* the bytes l (no NUL) then a NUL at p, as the walk reads them *)
Definition cstr (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p (l ++ [0]) /\ Forall (fun c => c <> 0) l.
(* what a runtime string reader needs of it: below the stack, shorter than 2^32 (donor k + 1 < 2^32, YG0d.v:407), its word reads inside one memory band
   (amem_range over len + 8; the interceptors' range check region_in_mem, a Theorem Labs lane), every byte up to the NUL addressable
   (the interceptor's range check), and the rest of the 8-byte word holding the NUL visible (musl's word reads; donor
   astrnlen_realizes, YG0d.v:411) *)
Definition cstr_ok (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  cstr W mem p l /\ 4096 <= p /\ p + Z.of_nat (length l) + 8 <= alloc_ceiling /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\
  amem_range p (Z.of_nat (length l) + 8) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l) + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l) + 1) /\
  (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     aview segs (w_H W) mem a <> None).
(* a byte window [p, p + n) of a C string's bytes, each visible *)
Definition bytes_at (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p l.

(* the non-owned part of the donor's rom_view (YG0d.v:382): every read-only byte that is not a runtime-owned static and
   not errno reads as the image byte. arodata_okP gives it at every state; rom_view itself is not provable for fm, whose
   .rodata global redzones are owned statics (A/AF0m.v:557) that no AR clause pins (Integrate). The runtime walks read
   only non-owned read-only bytes (musl's word constants, the formats). *)
(* (fuzz_disco.asan-ubsan: its 46 .rodata globals' redzones are owned statics too, and Tfib_const_abs already pins
   every owned read-only byte, so both halves are provable from AR (link-a/donor/rodata-R2.md (a working branch 88d3d5cd59df)); fm's fmi_rom_viewO moves with
   its tfib_rom_low bound 0x99000 -> 0xa0000.) *)
Definition rom_viewN (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

(* the owned part: every read-only byte that is a runtime-owned static (fm's .rodata global redzones and the runtime's
   read-only cells, A/AF0m.v:555-559) reads as the image byte. A runtime word read of a read-only string's NUL word
   reaches a redzone; the clean-memory transfer of the strlen, strchr, strncmp, memchr, strstr, strncasecmp and isalnum walks needs these bytes. Source: AR's
   constant cells, once Tfib_const pins every owned read-only byte to its image value (a Theorem Labs lane); the final instance
   proves it inside fm_img_facts. *)
Definition rom_viewO (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
End c.
