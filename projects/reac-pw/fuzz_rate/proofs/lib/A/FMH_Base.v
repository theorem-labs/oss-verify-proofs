(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMH_Base.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* fm program part, statement base: fm.asan addresses, the per-function stack/event/live constants, the user-poison
   wrappers over the donor's afn_pre / apost_base, C-string premises, fm's static allocation counters (fuzz/alloc.c).
   Definitions only. Design: port-fm design/HARNESS.md. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Base.v (cold/port-fm-rtprintf-param 3e35620c52e) *)
(* Modified by Theorem Labs, 2026-10 (h-decbox-a4, G9 row P8-A-base): fuzz_disco.asan's SUBSET of fm's file, the names
   the G9 snprintf route reads (g9/P0/pieces/P8-A-base.md): PC_snprintf, FM_GOT_canary, FM_canary, ecall_pre_k,
   ecall_preU_k, cstr, cstr_ok, bytes_at, rom_viewN, rom_viewO. Each kept Definition is fm's text; module paths changed;
   the three addresses are fuzz_disco.asan's, keyed by symbol + offset (g9/P0/numerals.tsv, FMH_Base.v rows 51 / 62 /
   63): PC_snprintf = __interceptor_trampoline_snprintf+0 (0x41314 -> 0x42a04), FM_GOT_canary = the .got slot that
   __stdio_write+0x30 / fmt_fp+0x60 / pad+0x20 name (0x9a638 -> 0xa1198), FM_canary = __stack_chk_guard+0
   (0x5f4db0 -> 0x5fc090). Dropped, fm's harness with no disco counterpart (numerals.tsv: HARNESS / UNRESOLVED, no
   route use): fm's other entries and targets, the fuzz/alloc.c statics and their footprint (FMPstat.v, not copied),
   fm's seven snprintf formats (disco's thirteen call-site formats are stated by SnFF's FF_disco over
   disco_fmt_lo / disco_fmt_hi, P2; s4printf/callsites.md), the STK_ / EV_ / LIVE_ / CNT bounds, afn_preU /
   apost_baseU, wdest_ok, fm_glob / fm_stat / fm_rblock, stk_sh0, str_homeA. No ManifestModel / YC20 Require. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fuzz_disco.asan addresses (symbol + offset, g9/P0/numerals.tsv) ---- *)
(* runtime entries the target code calls (interceptor trampolines `__wrap_*`) *)
Definition PC_snprintf : Z := 0x421d4.
(* stack protector cells musl's printf_core reads (donor A/AE2d.v:35-36 A_GOT_canary / A_canary at cgif_file addresses):
   the .got slot and __stack_chk_guard *)
Definition FM_GOT_canary : Z := 0x9caf8.
Definition FM_canary : Z := 0x5f7c10.

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

(* Poison's ecall_preU (Rt/SnUpoison.v) with STK bytes of stack *)
Definition ecall_preU_k (STK : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ecall_preU segs B ly S U W regs mem md /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).

(* ---- C strings ---- *)
(* the bytes l (no NUL) then a NUL at p, as the walk reads them *)
Definition cstr (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p (l ++ [0]) /\ Forall (fun c => c <> 0) l.
(* what a runtime string reader needs of it: below the stack, shorter than 2^32 (donor k + 1 < 2^32, YG0d.v:407), its word reads inside one memory band
   (amem_range over len + 8; the interceptors' range check region_in_mem, RtStr), every byte up to the NUL addressable
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
(* (fuzz_disco: its .rodata redzones are owned statics too, and Tfib_const_abs already pins them, so both halves are
   provable from AR: g9/P0/rodata-R2.md; fm's fmi_rom_viewO, with its tfib_rom_low bound 0x99000 -> 0x9f000, lands in
   G9 row P8-A-compose-cr, not here.) *)
Definition rom_viewN (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

(* the owned part: every read-only byte that is a runtime-owned static (fm's .rodata global redzones and the runtime's
   read-only cells, A/AF0m.v:555-559) reads as the image byte. A runtime word read of a read-only string's NUL word
   reaches a redzone; the clean-memory transfer of RtScan's / RtStr's walks needs these bytes (RtScan). Source: AR's
   constant cells, once Tfib_const pins every owned read-only byte to its image value (Reloc); the final instance
   proves it inside fm_img_facts. *)
Definition rom_viewO (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
End c.
