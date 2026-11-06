(* libreac/fuzz_boxreg, build asan (fuzz_boxreg.asan): the contract of the snprintf wrapper as the program code calls
   it, for the one format the program passes. Statement only (rule 24: no function proved); the runtime slice proves it.
   Entry: the trampoline __interceptor_trampoline_snprintf (0x41430, `j 0x452c0`; the listing's PTail / PCall of
   BS___interceptor_trampoline_snprintf, so a walk takes this contract at pa_sigma BS___interceptor_trampoline_snprintf)
   -> ___interceptor_snprintf 0x452c0 (frame 0x60) -> ___interceptor_vsnprintf 0x44ed0 (frames 0x7f0 + 0x80) ->
   REAL(vsnprintf) through the cell 0x9ac28 = musl vsnprintf 0x91aec -> vfprintf 0x8e9c0 -> printf_core 0x8eb70.
   The calls it serves (fuzz_boxreg.asan objdump): reac_boxreg_set_name's TAIL call `j 0x41430` at 0x81f10 (after
   `ld ra,8(sp); addi sp,sp,16`) and reac_boxreg_declare's `jal 0x41430` at 0x81984. Both pass the format "%s"
   (A_OBJ 10, 0x20d40) in a2, the size 32 in a1 and, as the destination in a0, the 32-byte name field r + 56 * i + 24
   of a row of the 288-byte registry struct, a heap block; the argument in a3 is the caller's name string or ""
   (A_OBJ 11, 0x20d60). So the contract is stated for that format only: f holds "%s" and its NUL, x a NUL-terminated
   string s.
   Content: Pau's model (lib/Prog/printf_facts_c.v, lib/Prog/snprintf_c.v) as it is: pf_parse [37; 115] = Some [Ps] and
   pf_text [Ps] [APtr s] = Some s, so the call writes firstn (n - 1) s ++ [0] at d (snprintf_c's
   pf_bytes (firstn (Z.to_nat (n - 1)) T ++ [0]) with T = s; asn_out below) and returns length s (snprintf_c's
   Z.of_nat (length T)). It writes nothing else outside its 2 * ESTACK window.
   Form: cgif_file_fuzzer's abcmp_realizes (lib/Reusable/YG0d.v:353-372) and fuzz_identity's astrlen_realizes
   (lib/A/Rt/StrlenDef.v at a working branch ea5560a967b): 2 * ESTACK of present stack below sp, the
   ranges it reads and writes outside that window, AR kept with the same ly S W, callee-saved registers kept, memory
   outside the window and the written bytes kept, presence kept.
   Stack: 8160 bytes below sp (amig's measure, SNPRINTF_WRAP_K in lib/A/Prog/snprintf_wrap_c.v at
   a working branch 67b70ae1ec3), inside the 2 * ESTACK = 8192 window; so a caller's STK is its frame at the
   call + 2 * ESTACK (CONVENTIONS section 4, as for bcmp).
   Floating-point state: a Theorem Labs lane's shared post (a working branch 401616133a7,
   FMsnprintfShared.v:142-145), verbatim: the return configuration is built with SOME fx' whose f registers equal the
   pre's except f10 and whose fcsr has rounding mode 0. A Theorem Labs lane measured the same freedom on the plain contract
   (printf_post, lib/Prog/printf_facts_c.v), and GXA's released pop_arg contract loses fa0 for every conversion
   (G_pop_arg.v:470-479), so a pinned-fx post is not provable from GXA as released (a Theorem Labs lane 03:44Z). A caller
   continues at fx' with a Theorem Labs lane's srr_fx_continue (FMsnprintfSx.v at ad235a56db0) and its `forall fx` contracts.
   Read footprint: the format bytes f .. f + 2 and their shadow (printf_common's check of the format, done when the flag
   byte check_printf *(0x98ea8) + 84 is set: `lbu a1,0x54(s4)` at 0x44f28); the string bytes x .. x + k and their shadow
   (printf_common's check of a %s argument; the checks of the strnlen and memchr interceptors that musl's printf_core
   reaches; the strnlen one is done when the flag byte intercept_strlen *(0x98ea8) + 251 is set: `lbu a1,0xfb(s5)` at
   0x41770; for either value of the two flags the result is the same); the rest of the 8-byte word that holds the NUL
   (musl memchr's word loop under strnlen, n = INT_MAX); the read-only image (asn_rom_kept: the constants musl's
   printf_core reads, each one that is neither an owned static nor an errno byte; an owned one is the runtime's and
   AR's as_const fixes it); and the runtime cells the wrappers read, which AR
   (as_const of this image's asyms) must fix, as for abcmp_realizes: real_vsnprintf 0x9ac28, real_strnlen 0x9acd0,
   real_memchr 0x9abe8, the flags pointer 0x98ea8, the shadow base pointer 0x98eb8 (amig's model of the same wrapper,
   lib/A/Prog/vsnprintf_wrap_c.v at 67b70ae1ec3, also names real_vfprintf 0x9ac20 and the guard word 0x99b40 ->
   0x5f3f50). The destination's presence, ownership and shadow come from AR's block and shadow laws (al_blocks,
   al_shadow) for the heap block (p, m); ___interceptor_vsnprintf's write check covers d .. d + min (n, k + 1) - 1.
   Why asn_rom_kept and not rom_view (YG0d.v:382): a caller calls snprintf after other calls, and an ajournal keeps
   an image byte only when it is neither an owned static nor an errno byte (lib/Reusable/YCbq.v:362), while an asyms
   in cgif's form owns read-only bytes (cgif lib/A/AF0m.v:280-287 Tfib_owned_static holds 0x102e8, 0x20e0d, ... of the
   read-only segment; AR's am_const_owned asks every const cell to be owned). So rom_view does not survive a call,
   but asn_rom_kept does: it is arodata_okP (lib/A/Prog/BoxBase.v, carried by arodata_ok_journalP) on the read-only
   segments. After the contract, three more facts from which a caller re-derives at its call the premises an
   ajournal does not carry (YCbq.v:358 keeps no byte below alloc_ceiling outside the blocks, so no shadow byte of the
   image and no chunk tail): asn_rom_bytes and asn_rom_str (bytes and strings of the read-only image that are no
   owned static and no errno byte, which asn_rom_kept then gives; state-free), and asn_blk_tail_vis (in every AR
   state a heap block's last 8-byte word is readable past its requested size). The shadow of the image's strings
   comes from lib/A/Prog/BoxRo.v (globs_marked, img_shadow_vis), which hold in every AR state.
   The interceptor-metadata map (AddrHashMap<CommonInterceptorMetadata, 31051>): the contract has no premise on it, as
   cgif's non-FILE interceptor contracts have none (lib/Reusable/YG0d.v abcmp_realizes, aintrin_realizes; cgif
   lib/A/AE2s.v:710 bcmp_icpt_contract is proved from AR_laws and the symbols alone; only cgif's FILE contracts and the
   program functions that call a FILE function carry ameta_inv). Measured on fuzz_boxreg.asan (capstone control-flow
   scan, 2026-10-28): the map's pointer interceptor_metadata_map (0xa07c0, pointing to metadata_mem 0xa07c8) is
   addressed directly only by the fflush interceptor (0x463c4), which this call could reach only through
   BufferedStackTrace::UnwindImpl (0x59e40) -> UnwindSlow -> _Unwind_Backtrace -> logUnwinding -> fflush. Each
   UnwindImpl call on the path is on a report branch: ___interceptor_vsnprintf calls it at 0x450a0 only after the
   size-overflow test of its write check (0x44f80 bltu / 0x45054 bgeu -> 0x45058) and at 0x45184 only when
   __asan_region_is_poisoned (0x45110) returns nonzero (0x4511c beqz not taken); printf_common (0x44354) at 0x44984,
   0x449ec, 0x44a90, 0x44b30, 0x44cd0 and 0x44da4, each behind one of the same two tests (overflow 0x443b8, 0x44790,
   0x44888; poisoned 0x44914, 0x44a20, 0x44d3c); ___interceptor_strnlen (0x41714) at 0x41860 / 0x41944 (overflow
   0x4178c / 0x41814; poisoned 0x418dc); ___interceptor_memchr (0x431a8) at 0x43328 / 0x43414 (overflow 0x43218 /
   0x432d4; poisoned 0x433a4); ___interceptor_snprintf calls it nowhere. The premises exclude both tests for every
   range the wrappers check: amem_range and the bounds on n (no wrap of f + 3, x + k + 1, d + n) and
   range_addressable / shadow_hull_vis of f and x and AR's shadow law for the block of d (no poisoned byte). The other
   callees on the normal path are TryAsanInitFromRtl (0x590a8, which returns at once when asan_inited 0xa1c58 is 1),
   REAL(vsnprintf), REAL(strnlen) and REAL(memchr) (musl), and printf_common's Report (its unexpected-specifier
   warning) and CheckFailed, which the format "%s" does not reach (compiler-rt's printf_common; not walked here). So
   no state that meets the premises reaches the map, whatever the environment. Of the runtime entries the program
   calls, only malloc and free unwind on their normal path (request_fast = common_flags()->fast_unwind_on_malloc, offset 0x22 of common_flags_dont_use 0x132aa8, default 1 set by CommonFlags::SetDefaults 0x60d7c; ASAN_OPTIONS is never read because __sanitizer::GetEnv 0x63eec returns NULL whenever its RELRO GOT word 0x98ef8 is nonzero, and the image holds 1 there; so they tail-jump to UnwindFast and never reach UnwindSlow / libunwind; the report paths, with fast_unwind_on_fatal / _on_check default 0, are the branches the premises exclude; table: a Theorem Labs lane's boxpa/unwind-reach.md);
   their contracts are cgif's (amalloc_realizes, afree_realizes), not this file's. 
   R2 exit form (a Theorem Labs lane 00:09Z): fast_unwind_on_fatal / _on_check are 0, so a report or CheckFailed entry, if executed, reaches libunwind's _LIBUNWIND_ABORT sites; this contract admits no state that reaches one (the premises refute the branches above), and a walk that uses it must end any such route at the entry as a refusal (ok_or_refused), never step into it. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* The format the program passes: "%s" and its NUL. *)
Definition ASN_FMT : list Z := [37; 115; 0].
(* The bytes a call writes at the destination for the size n and the string s. *)
Definition asn_out (n : Z) (s : list Z) : list Z := firstn (Z.to_nat (n - 1)) s ++ [0].
(* One past the 8-byte word that holds the byte at x + k (the NUL of a string of length k at x). *)
Definition asn_word_end (x k : Z) : Z := x + k - (x + k) mod 8 + 8.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* The read-only image as every call keeps it: a byte of a read-only segment that is neither an owned static nor an
   errno byte reads as the image's byte. *)
Definition asn_rom_kept (W : world segs) (mem : word -> option byte) : Prop :=
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
(* Discharge route (a Theorem Labs lane 23:56Z; measured in a Theorem Labs lane's boxreg/GXA-FIT.md): the printf core
   below this call is fuzz_reply's released GXA (origin/ossv/recipes proofs/plugin-hostd/fuzz_reply/lib/CJ/RL/GXA/,
   G_vfprintf_snf_closed.v:108 vfprintf_snf_a_closed over vfprintf_snf_a_stmt {IMG : RImg}), instantiated at an RImg for
   fuzz_boxreg.asan (all 25 GXA keys exist here; 2758 / 2758 instructions of the eight walked functions pair with
   fuzz_reply's, 0 differing); GXA's post covers truncation (buffer firstn N o ++ [0], a0 = untruncated length), which
   this contract needs (names up to 47 characters into n = 32). The path is trampoline 0x41430 -> __interceptor_snprintf
   0x452c0 -> __interceptor_vsnprintf 0x44ed0 (printf_common, REAL(vsnprintf) cell 0x9ac28) -> musl vsnprintf 0x91aec
   -> __wrap_vfprintf -> __interceptor_vfprintf -> REAL(vfprintf) cell 0x9ac20 -> vfprintf 0x8e9c0 (GXA); no musl
   snprintf frame. GXA does not cover the interceptor layers, musl vsnprintf, its SPEC_memcpy / memset / strnlen /
   pop_arg parameters, nor the bridge from GXA's evt / RImg conclusion to this SRr / AR statement (exists nowhere yet);
   so this statement stays the call-level hypothesis the walks take, and its proof = GXA instance + that glue. *)
Definition asnprintf_realizes (pc : Z) : Prop :=
forall ly S W regs mem md d n f x (s : list Z) p m,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 x ->
(* the destination: n bytes of a heap block, outside the window *)
1 <= n < 2 ^ 31 ->
In (p, m) (ablocks B ly S) -> p <= d -> d + n <= p + m ->
(forall a, d <= a < d + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(* the format "%s" *)
(forall i, 0 <= i < 3 -> aview segs (w_H W) mem (f + i) = Some (nth (Z.to_nat i) ASN_FMT 0)) ->
0 < f -> amem_range f 3 ->
(* R2 (a Theorem Labs lane 15:05Z): the GXA route proves snprintf only for a format in the read-only image below the GOT canary
   slot (a Theorem Labs lane's FMsnprintfFmI.v:32-37 FF_fm at 3e35620c52e; the seam's 65536 <= fam_lo, fam_hi <= GOT slot) *)
0x10000 <= f -> f + 3 <= 0x99b40 ->
(forall a, f <= a < f + 3 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> (f + 3 <= d \/ d + n <= f) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF f 3 -> shadow_hull_vis (aview segs (w_H W) mem) f 3 ->
(* the argument: the string s and its NUL at x, and the rest of the NUL's 8-byte word *)
Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 -> 0 < x ->
(forall i, 0 <= i <= Z.of_nat (length s) -> aview segs (w_H W) mem (x + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) ->
(forall a, x + Z.of_nat (length s) < a < asn_word_end x (Z.of_nat (length s)) -> aview segs (w_H W) mem a <> None) ->
(* R2: printf_common reads the string's aligned 8-byte shadow hull (a Theorem Labs lane's RT_pf_sh.v:159-162 pf_args_amem), so the
   address bound covers |s| + 8 bytes, not |s| + 1 *)
amem_range x (Z.of_nat (length s) + 8) ->
(forall a, x <= a < asn_word_end x (Z.of_nat (length s)) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(asn_word_end x (Z.of_nat (length s)) <= d \/ d + n <= x) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length s) + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length s) + 1) ->
asn_rom_kept W mem ->
(* frm0 at entry: GXA's released VfprintfCall.v:37 needs rounding mode 0 at musl vfprintf's entry, so a Theorem Labs lane's
   shared contract takes it (a working branch a3877b821d6). The caller supplies it: fx0's fcsr
   is 0 (lib/Reusable/YK11.v:16) and no boxreg program function holds an f* or csr* instruction (measured on both
   originals), so the rounding mode is the start-up one at every call. *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length s)) /\
(forall i, 0 <= i < Z.of_nat (length (asn_out n s)) ->
aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (asn_out n s) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length (asn_out n s))) ->
~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* [a, a + length l) lies in the image's read-only segments, holds the bytes l there, and is neither an owned static
   nor an errno byte; so asn_rom_kept reads it as l. *)
Definition asn_rom_bytes (a : Z) (l : list Z) : Prop :=
forall i, 0 <= i < Z.of_nat (length l) -> in_rom segs (a + i) /\
~ Exists (in_zr (a + i)) (as_owned_static B) /\ ~ (as_errno B <= a + i < as_errno B + 4) /\
option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (a + i))) = Some (nth (Z.to_nat i) l 0).
(* The string s and its NUL at x are such bytes. The rest of the NUL's 8-byte word, which musl's memchr word loop
   reads, is image data of any value, and MAY be a runtime-owned static: boxreg's two empty strings 0x20ce0 and
   0x20d60 have their word tails inside the owned right redzones (0x20ce1, 0x1f) and (0x20d61, 0x1f) of the
   generated table, so the earlier form of this definition, which asked the tail to be unowned, was unsatisfiable
   at boxreg's own instances (found by two Theorem Labs lanes, 2026-10-29 06:40Z). The
   caller needs only that those bytes are readable: aview reads through mbyte, which falls back to the image byte
   when memory holds none (lib/Reusable/YG0n.v:18, YP09.v:18-22), so `seg_rom ... <> None` gives it in every state. *)
Definition asn_rom_str (x : Z) (s : list Z) : Prop :=
asn_rom_bytes x (s ++ [0]) /\
(forall a, x + Z.of_nat (length s) < a < asn_word_end x (Z.of_nat (length s)) ->
 in_rom segs a /\ seg_rom segs (Z_to_bv 64 a) <> None).
(* In every state, the bytes of a heap block's last 8-byte word past its requested size are readable: they are the
   block's chunk tail, which AR keeps visible (am_junk over chunk_junk, lib/Reusable/YG0n.v:55-60, :219). *)
Definition asn_blk_tail_vis : Prop :=
forall ly S (W : world segs) mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + n <= a < p + round_up n 8 -> aview segs (w_H W) mem a <> None.
End c.
End b.
