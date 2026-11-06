(* Image B twin of lib/A/RT_pf_Tbl.v at d49bd1db505: module paths lib.A -> lib.B; 56 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) (* The numerals of fuzz_reply.asan-ubsan's snprintf interceptor chain (RT_pf_stmt.v and its proofs), one name each.
   Source: the pinned image's objdump and nm (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) and fuzz_reply.nm.txt (sha256 544ac719824e; internal record) of the asan-ubsan build,
   fuzz_reply.nm.txt (sha256 544ac719824e; internal record)).  Every one of these values is also checked by the relocated Bz walk that carries it
   (lib/B/Bz/K/I_snprintfw.v, I_vsnprintfw.v, I_vfprintfw.v, I_vfprintfw1.v, I_vprintfw.v): a wrong value here makes
   the matching proof fail to compile, it cannot make a statement vacuous.

   THE CHAIN (there is no musl snprintf frame in the ASan image):
     __wrap_snprintf 0x42234 = __interceptor_trampoline_snprintf: `j 46928`
       -> ___interceptor_snprintf 0x46928: frame 96, va_start spill, TryAsanInitFromRtl, `jal 46538`
       -> ___interceptor_vsnprintf 0x46538 (also reached from __wrap_vsnprintf 0x4222c = `j 46538`):
          frame 2032 + 128 = 2160, TryAsanInitFromRtl, printf_common 0x459bc (check_printf = 1),
          REAL(vsnprintf) through the cell 0x9fcf0 (= musl vsnprintf 0x963b4) by `jalr a4` at 0x465c8,
          then the write-range check of the output (__asan_region_is_poisoned) and return
       -> musl vsnprintf 0x963b4: frame 304, `jal 42228` at 0x96450
       -> __wrap_vfprintf 0x42228 = `j 46484`
       -> ___interceptor_vfprintf 0x46484: frame 48, TryAsanInitFromRtl, printf_common, REAL(vfprintf) through the
          cell 0x9fce8 (= musl vfprintf 0x93288) by `jalr a3` at 0x464f0
       -> musl vfprintf 0x93288 (GXA's closed body, at RT_IImgA.v's A_img).

   MEASURED: ___interceptor_snprintf's va_start SPILL (objdump lines 22972-22994), with q = sp at entry:
     0x46928  addi sp,sp,-96            frame [q-96, q)
     0x46948  sd   a7,88(sp)            [q-8]   <- a7  (5th variadic word)
     0x4694c  sd   a3,56(sp)            [q-40]  <- a3  (1st variadic word)
     0x46950  sd   a4,64(sp)            [q-32]  <- a4
     0x46954  sd   a5,72(sp)            [q-24]  <- a5
     0x46958  sd   a6,80(sp)            [q-16]  <- a6
     0x4695c  addi a0,sp,56             va_list = q-40
     0x46960  sd   a0,8(sp)             [q-88]  <- va_list
     0x4696c  ld   a3,8(sp)             a3 = va_list = q-40, passed to ___interceptor_vsnprintf (jal 0x4697c)
   So the va_list walks [q-40, q) (the spilled a3..a7) and then CONTINUES INTO THE CALLER'S FRAME at [q, q+8k) for the
   6th, 7th, ... variadic word: the spill is contiguous with the caller's outgoing stack words only because the
   spill ends exactly at q.  GXA's va_list walk (G_vsnprintf.v:164-174 / va_area) reads that area; it does not build it.

   MEASURED: own stack depths (frame + the deepest callee window each lemma below charges):
     ___interceptor_snprintf     frame 96;   TryAsanInitFromRtl 16 below it (Bz snprintf_walkA: lo <= q - 112)
     ___interceptor_vsnprintf    frame 2160; TryAsanInitFromRtl 16 below (lo <= q - 2176); printf_common 2320 below
                                 its frame (lo <= q - 4480, Bz vsnprintf_walkAc); the output check 80 below
                                 (lo <= q - 2240, vsnprintf_walkCm); REAL(vsnprintf) VSN_DEPTH = 5904 below its frame
     printf_common 0x459bc       frame 2032 + 208 = 2240; its callees 80 below (PCOM_DEPTH = 2320)
     ___interceptor_vfprintf     frame 48;   TryAsanInitFromRtl 16 below (lo <= q - 64); printf_common 2320 below
                                 its frame (lo <= q - 2368, vfprintf_walkA); REAL(vfprintf) 48 + VF_DEPTH below its
                                 frame (GXA's guarded body statement, VfprintfCall.v:35)
   WINDOW PREMISES that follow:  ___interceptor_vsnprintf: lo <= q - (2160 + 5904) = q - 8064;
                                 ___interceptor_snprintf:  lo <= q - (96 + 2160 + 5904) = q - 8160;
                                 ___interceptor_vfprintf:  lo <= q - (48 + 48 + 5552) = q - 5648, 48 more than the
                                 48 + VF_DEPTH = 5600 musl vsnprintf grants its vfprintf call - carried by
                                 RT_pf_stmt.v's vf_ready_icpt, so a vsnprintf caller grants 304 + 5648 = 5952. *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

(* entries *)
Definition PF_WRAP_SNPRINTF : Z := 0x42234.        (* __wrap_snprintf = __interceptor_trampoline_snprintf *)
Definition PF_ICPT_SNPRINTF : Z := 0x46928.        (* ___interceptor_snprintf *)
Definition PF_WRAP_VSNPRINTF : Z := 0x4222c.       (* __wrap_vsnprintf = __interceptor_trampoline_vsnprintf *)
Definition PF_ICPT_VSNPRINTF : Z := 0x46538.       (* ___interceptor_vsnprintf *)
Definition PF_WRAP_VFPRINTF : Z := 0x42228.        (* __wrap_vfprintf = __interceptor_trampoline_vfprintf *)
Definition PF_PRINTF_COMMON : Z := 0x459bc.        (* printf_common(void*, const char*, va_list) *)

(* return addresses inside the interceptors *)
Definition PF_RA_SNF_VSN : Z := 0x46980.           (* ___interceptor_snprintf's call of ___interceptor_vsnprintf *)
Definition PF_RA_VSN_PCOM : Z := 0x465b0.          (* ___interceptor_vsnprintf's printf_common call *)
Definition PF_RA_VSN_REAL : Z := 0x465cc.          (* ___interceptor_vsnprintf's REAL(vsnprintf) call *)
Definition PF_RA_VF_PCOM : Z := 0x464dc.           (* ___interceptor_vfprintf's printf_common call *)
Definition PF_RA_VF_REAL : Z := 0x464f4.           (* ___interceptor_vfprintf's REAL(vfprintf) call *)

(* the strings the interceptors pass printf_common as its first argument *)
Definition PF_STR_VSNPRINTF : Z := 0x17944.        (* "vsnprintf" *)
Definition PF_STR_VFPRINTF : Z := 0x1eac1.         (* "vfprintf" *)

(* runtime cells the interceptors read *)
Definition PF_ASAN_INITED : Z := 0xa7318.          (* __asan::asan_inited (byte, = 1 after start-up) *)
Definition PF_GOT_COMMON_FLAGS : Z := 0x9df40.     (* GOT word of __sanitizer::CommonFlags common_flags_dont_use *)
Definition PF_COMMON_FLAGS : Z := 0x138168.        (* common_flags_dont_use *)
Definition PF_CHECK_PRINTF : Z := 0x1381bc.        (* common_flags_dont_use + 0x54: check_printf (byte, = 1) *)
Definition PF_REAL_VSNPRINTF : Z := 0x9fcf0.       (* __interception::real_vsnprintf *)
Definition PF_REAL_VFPRINTF : Z := 0x9fce8.        (* __interception::real_vfprintf *)
Definition PF_MUSL_VSNPRINTF : Z := 0x963b4.       (* musl vsnprintf (RT_IImgA.v KV 0x1d084 / 0x7f000200) *)
Definition PF_MUSL_VFPRINTF : Z := 0x93288.        (* musl vfprintf (RT_IImgA.v KV 0x18554 / 0x7f000400) *)

(* frame sizes and windows (measured above) *)
Definition PF_SNF_FRAME : Z := 96.
Definition PF_VSN_FRAME : Z := 2160.
Definition PF_VF_FRAME : Z := 48.
Definition PF_SPILL : Z := 40.                     (* the spilled a3..a7: [q - 40, q) *)
Definition PF_PCOM_DEPTH : Z := 2320.             (* printf_common's window, = I_vprintfw.v PCOM_DEPTH *)
Definition PF_TRYINIT : Z := 16.                  (* TryAsanInitFromRtl's frame *)

(* values of A_img's symbol map the chain proofs need as numbers (RT_IImgA.v rows KV 0x22e18 / 0x34288 / 0x35000;
   RT_pf_kit.v proves each equal to the map's value by vm_compute) *)
Definition PF_GOT_SSP : Z := 0x9ebd8.              (* GOT word of __stack_chk_guard *)
Definition PF_SSP_GUARD : Z := 0x5f9a30.           (* __stack_chk_guard *)
Definition PF_GLOBALS_TOP : Z := 0x5fc000.         (* GXA's GLOBALS_TOP: last PT_LOAD end rounded to a page *)
