(* libreac/fuzz_boxreg, build asan-ubsan: the contract of the strncmp wrapper as the program code calls it, in the form
   a Theorem Labs lane's shared runtime contract states it, so that boxreg's instance IS fm's statement and fm's proof relocates
   onto it (a Theorem Labs lane's "one of everything", 2026-10-28 22:28Z; a Theorem Labs lane's 22:38Z row).
   Source of the form: a working branch 445e498a469, proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Rt.v:124
   `astrncmp_realizes` (proved at lib/A/FMstrncmp.v `astrncmp_holds` for fm's image), over FMH_Base.v's
   STK_RT_STR / ecall_pre_k / cstr / cstr_ok / rom_viewN (:218) / rom_viewO (:227) and FMH_Rt.v's rt_post_ro and
   strn_eq. Those bodies are repeated here with an `abfm_` prefix, verbatim except that `rdW W mem` is written out as
   `mrestrict (w_H W) mem` (FMH_Base.v:138 Abbreviation) and `alloc_ceiling` as `ASAN_CEIL` (YG0f.v, the same RunCeil
   field); when the relocated FMH_Base / FMH_Rt land in this unit, this file takes them by name and drops the copies.
   Entry: the trampoline __interceptor_trampoline_strncmp 0x41458 (word 0x2e90006f, `j 0x41f40`), fm's PC_strncmp
   0x412d4 (`j 0x41dc4`); the two trampolines and the two interceptor bodies are the same code (whole functions as
   mnemonic + register sequences with immediates masked: 1/1 and 374/374, 0 differing; startcmp.py (sha256 5e24b81a4734; internal record)).
   With asan_inited = 1 the interceptor compares the bytes itself (loop 0x41fa4-0x41fc4), checks min(k + 1, n) bytes
   of each string, and returns sgn(s1[k] - s2[k]), or 0 at k = n; it reaches neither musl strncmp nor
   internal_strncmp on that path. Stack: 2256 bytes below sp, inside STK_RT_STR = 2 * ESTACK.
   Calls it serves (fuzz_boxreg.asan-ubsan): 0x80698, 0x808a4, 0x80c3c. All six sites of the two builds test the result
   against zero only (fuzz_boxreg.c:182, :266, :394 are `strncmp(...) != 0`; a Theorem Labs lane confirmed the walks read it
   with bnez), so fm's zero-test answer is what the program needs and the earlier sign form is dropped.
   The read-only premises are fm's two views, not the whole image: abfm_rom_viewN (every read-only byte that is not a
   runtime-owned static and not errno reads as the image byte; arodata_okP gives it at every state, and it is the
   text of lib/A/Rt/MemchrDef.v's kept read-only view) and abfm_rom_viewO (every read-only byte that IS a runtime-owned
   static reads as the image byte; AR's const law gives it from the 26 read-only pins af0m.py appends to
   Tfib_const_abs, generated B YF0m, af0m.py 2ac2dbe2).
   R2 (a Theorem Labs lane's row 29; reason as measured by a Theorem Labs lane's boxpa/unwind-reach.md,
   23:51Z / 23:55Z): NOT needed here. Of the 91 BufferedStackTrace::UnwindImpl call sites, the 4 allocation ones take
   request_fast = fast_unwind_on_malloc = 1 and go to UnwindFast, never to libunwind's abort / trace-print fflush; the
   other 87 are fatal-report / CheckFailed paths (fast_unwind_on_fatal / on_check = 0). The compiled defaults hold
   because ASAN_OPTIONS is never read: __sanitizer::GetEnv (A 0x63eec, B 0x63f4c) returns NULL when its RELRO GOT word
   (A 0x98ef8, B 0x99318) is nonzero, and both images hold 1 there (re-read here). This interceptor reaches UnwindImpl
   only on its report branch, which the premises exclude (the checked bytes are addressable). The only live
   AddrHashMap path is the harness exit guard -> __wrap_fflush, which concerns driver-class statements, not this one.
   So no asrc_meta_inv pin and no environment premise. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI04 YI00 YM05.
Import ListNotations.
Open Scope Z_scope.
Definition ABSTRNCMP_ENTRY : Z := 0x41458.
(* FMH_Rt.v:27: strncmp (s1, s2, k) = 0 is "the first k bytes of each string with its NUL agree" (C stops at the
   first NUL). *)
Definition abfm_strn_eq (k : nat) (l1 l2 : list Z) : Prop := firstn k (l1 ++ [0]) = firstn k (l2 ++ [0]).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* FMH_Base.v: the stack the string runtime entries take. *)
Definition ABFM_STK_RT_STR : Z := 2 * ESTACK.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* FMH_Base.v ecall_pre_k: the donor's call precondition with a deeper, present window. *)
Definition abfm_ecall_pre_k (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
  ecall_pre segs B ly S W regs mem md /\ ASAN_CEIL <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).
(* FMH_Base.v cstr / cstr_ok: a C string of bytes l at p, with the room and the shadow the interceptor reads. *)
Definition abfm_cstr (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (mrestrict (w_H W) mem) p (l ++ [0]) /\ Forall (fun c => c <> 0) l.
Definition abfm_cstr_ok (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  abfm_cstr W mem p l /\ 4096 <= p /\ p + Z.of_nat (length l) + 8 <= ASAN_CEIL /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\
  amem_range p (Z.of_nat (length l) + 8) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l) + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l) + 1) /\
  (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     aview segs (w_H W) mem a <> None).
(* FMH_Base.v:218 rom_viewN: every read-only byte that is not a runtime-owned static and not errno reads as the image
   byte. *)
Definition abfm_rom_viewN (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
(* FMH_Base.v:227 rom_viewO: every read-only byte that is a runtime-owned static reads as the image byte. *)
Definition abfm_rom_viewO (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
(* FMH_Rt.v rt_post_ro: return to ra with AR kept, callee-saved registers kept, the answer in a0 under R, and the
   write set inside [sp - STK, sp). *)
Definition abfm_rt_post_ro (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) ->
       aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
(* FMH_Rt.v:124, at boxreg's entry. *)
Definition abstrncmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y n (l1 l2 : list Z),
  abfm_ecall_pre_k ABFM_STK_RT_STR ly S W regs mem md -> abfm_rom_viewN W mem -> abfm_rom_viewO W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  abfm_cstr_ok W mem x l1 -> abfm_cstr_ok W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (abfm_rt_post_ro ABFM_STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> abfm_strn_eq (Z.to_nat n) l1 l2)).
End c.
End b.
