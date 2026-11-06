(* fm runtime layer, statement base: the runtime entries fm's target code calls, the stack each runtime call asks for,
   and the premises of a runtime call (ecall_pre with STK bytes of stack, C strings, the read-only image views).
   Definitions only; no program module. The program part (lib/A/FMH_Base.v) re-exports this file. *)
(* Relocated to plugin-hostd/fuzz_command from omx-clap-core/fuzz_manifest's program-free split
   (proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_RtBase.v): module paths; the one entry used here (strncmp) at this
   image's trampoline; fm's poison-window premise (ecall_preU_k) and fm's other entries and windows left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YI16 YK06 YM05.
Import ListNotations.
Local Open Scope Z_scope.

(* runtime entries the target code calls: the strncmp trampoline of fuzz_command.asan (`j 0x43b40`, A/Bz/A/I_tramp.v
   tramp_strncmp; RtString.v:28) *)
Definition PC_strncmp : Z := 0x43050.

(* runtime calls: what each runtime contract (RtBzHStr.v) asks below the call's sp *)
Definition STK_RT_STR : Z := 2 * ESTACK.      (* strncmp *)

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

(* ---- C strings ---- *)
(* the bytes l (no NUL) then a NUL at p, as the walk reads them *)
Definition cstr (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p (l ++ [0]) /\ Forall (fun c => c <> 0) l.
(* what a runtime string reader needs of it: below the stack, shorter than 2^32 (donor k + 1 < 2^32, YG0d.v:407), its word reads inside one memory band
   (amem_range over len + 8; the interceptors' range check region_in_mem), every byte up to the NUL addressable
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
Definition rom_viewN (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

(* the owned part: every read-only byte that is a runtime-owned static (fm's .rodata global redzones and the runtime's
   read-only cells, A/AF0m.v:555-559) reads as the image byte. A runtime word read of a read-only string's NUL word
   reaches a redzone; the clean-memory transfer of the runtime string walks needs these bytes. Source: AR's
   constant cells, once Tfib_const pins every owned read-only byte to its image value (Reloc); the final instance
   proves it inside fm_img_facts. *)
Definition rom_viewO (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
End c.
