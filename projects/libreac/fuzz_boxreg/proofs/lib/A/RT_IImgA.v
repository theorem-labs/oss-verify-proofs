(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from plugin-hostd/fuzz_reply's lib/A/RT_IImgA.v (a Theorem Labs lane,
   a working branch e51895d5655) for libreac/fuzz_boxreg's fuzz_boxreg.asan: module paths changed and every
   address re-derived for this image by the same rules (generator: a Theorem Labs lane's genimga_box.py). *)
(* The RImg instance of the ASan printf core (plugin-hostd/fuzz_reply's lib/CJ/RL/GXA, the one musl printf
   proof) on the pinned fuzz_boxreg.asan.  GXA's facts at this instance are checked by RT_IImgA_ok.v, which is
   the same file in every unit; this file carries every image numeral.

   HOW EACH ROW WAS DECIDED (never by value, never by a uniform delta):
     SYMBOL   the donor address is carried to fuzz_boxreg.plain by the released IImgP map
              (lib/CJ/RL/I/IImgP.v), and the plain address lies in a named symbol that this ASan image
              also has; the row keeps the offset inside the symbol.  Plain and ASan sizes agree on every
              one of these rows.
     CONTENT  the plain object's bytes occur exactly once in this image's .rodata.
     CODEREF  the object is named by an auipc/addi (or auipc/ld) pair, or is the jal target, inside a
              function of the chain in both images.  musl's calls to memcpy / memset / strnlen / wctomb /
              strerror go through the ASan INTERCEPTOR TRAMPOLINES, so those keys name the trampolines,
              not musl's own bodies: GXA assumes a call contract at each of these symbols, and the symbol
              must name the object the code jumps to.
     GEOMETRY an image bound (the last PT_LOAD end, rounded to a page). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.libreac.fuzz_boxreg.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).

Definition A_segs : list Segment := OSSVerify.libreac.fuzz_boxreg.images.Asan.M.loaded_segments.

Definition A_exact : list (Z * Z) := [
  KV 0x1029e 0x10b54;   (* CONTENT: musl printf prefix "-+   0X0x" (plain 0x10298), unique in asan .rodata on its 10 bytes *)
  KV 0x102a8 0x12ea3;   (* CONTENT: key-space "%s\n" (Printf_model FMT_emit); the only NUL-preceded match in asan .rodata, 4 bytes with its NUL *)
  KV 0x102bf 0x1475c;   (* CONTENT: unique in asan .rodata on 24 bytes *)
  KV 0x102e5 0x157df;   (* CONTENT: unique in asan .rodata on 32 bytes *)
  KV 0x1032a 0x19639;   (* CONTENT: unique in asan .rodata on 32 bytes *)
  KV 0x1034b 0x1d605;   (* CONTENT: unique in asan .rodata on 32 bytes *)
  KV 0x10355 0x1d605;   (* CONTENT: unique in asan .rodata on 32 bytes *)
  KV 0x1036a 0x1d61a;   (* CONTENT: unique in asan .rodata on 16 bytes *)
  KV 0x103b3 0x20504;   (* CONTENT: musl printf's "(null)" string (plain 0x1038b), unique in asan .rodata on its 7 bytes *)
  KV 0x10884 0x21f38;   (* CODEREF: printf_core's jump table: the auipc/addi pair at printf_core+0x534 in both images (plain 0x104a8), 0x148 below `states`; first word 0x6d180 = printf_core + 1352 - 0x21f38, as GRoTab.v's ROT_0x10884 computes *)
  KV 0x10964 0x22018;   (* CODEREF: printf_core's second table (plain 0x10588): the auipc/addi pair at printf_core+0x6ac in both images, 0x68 below `states` *)
  KV 0x10984 0x22038;   (* CODEREF: pop_arg's jump table (plain 0x105a8): the only .rodata reference inside pop_arg in both images, 0x48 below `states`; first word gives pop_arg + 40, as ROT_0x10984 *)
  KV 0x109cc 0x22080;   (* SYMBOL: symbol states+0x0 (plain size 464, asan size 464) *)
  KV 0x10b9c 0x22250;   (* SYMBOL: symbol xdigits+0x0 (plain size 16, asan size 16) *)
  KV 0x134a8 0x7ff04;   (* SYMBOL: symbol emit_printf+0x0 (plain size 72, asan size 72) *)
  KV 0x15f04 0x88658;   (* SYMBOL: symbol __stack_chk_fail_local+0x0 (plain size 8, asan size 8) *)
  KV 0x15f44 0x88660;   (* SYMBOL: symbol __errno_location+0x0 (plain size 12, asan size 12) *)
  KV 0x17d50 0x8e600;   (* SYMBOL: symbol __fwritex+0x0 (plain size 312, asan size 312) *)
  KV 0x17f40 0x8e7f0;   (* SYMBOL: symbol __towrite+0x0 (plain size 84, asan size 84) *)
  KV 0x183bc 0x8de7c;   (* SYMBOL: symbol __stdio_write+0x0 (plain size 400, asan size 400) *)
  KV 0x18554 0x8e9c0;   (* SYMBOL: symbol vfprintf+0x0 (plain size 432, asan size 432) *)
  KV 0x18704 0x8eb70;   (* SYMBOL: symbol printf_core+0x0 (plain size 3632, asan size 3632) *)
  KV 0x19534 0x8f9a0;   (* SYMBOL: symbol pop_arg+0x0 (plain size 308, asan size 308) *)
  KV 0x19668 0x8fad4;   (* SYMBOL: symbol pad+0x0 (plain size 212, asan size 212) *)
  KV 0x1973c 0x8fba8;   (* SYMBOL: symbol fmt_fp+0x0 (plain size 5832, asan size 5832) *)
  KV 0x1ae04 0x41440;   (* CODEREF: jal target of strerror in printf_core: __interceptor_trampoline_strerror *)
  KV 0x1ae48 0x4143c;   (* CODEREF: jal target of wctomb in printf_core: __interceptor_trampoline_wctomb *)
  KV 0x1af98 0x81f44;   (* SYMBOL: __extenddftf2 (plain 0x196a8, size 400 in both images; pop_arg's jal target) *)
  KV 0x1cfb4 0x91ad0;   (* SYMBOL: symbol vprintf+0x0 (plain size 28, asan size 28) *)
  KV 0x1d084 0x91aec;   (* SYMBOL: symbol vsnprintf+0x0 (plain size 204, asan size 204) *)
  KV 0x1d150 0x91bb8;   (* SYMBOL: symbol sn_write+0x0 (plain size 220, asan size 220) *)
  KV 0x21334 0x51094;   (* CODEREF: jal target of memcpy in sn_write and __fwritex: __interceptor_trampoline_memcpy (= __wrap_memcpy) *)
  KV 0x21738 0x51090;   (* CODEREF: jal target of memset in printf_core, pad and vsnprintf: __interceptor_trampoline_memset (= __wrap_memset) *)
  KV 0x21920 0x413f0;   (* CODEREF: jal target of strnlen in printf_core: __interceptor_trampoline_strnlen *)
  KV 0x22e18 0x99b40;   (* CODEREF: the GOT word for the stack guard: auipc/ld at printf_core+0x64 and in vsnprintf (ld s2 at 0x91b10) both form 0x99b40 *)
  KV 0x23f60 0x9d568;   (* SYMBOL: symbol __stdout_FILE+0x0 (plain size 232, asan size 232) *)
  KV 0x34288 0x5f3f50;   (* SYMBOL: symbol __stack_chk_guard+0x0 (plain size 8, asan size 8) *)
  KV 0x35000 0x5f6000;   (* GEOMETRY: last PT_LOAD end 0x5f57f0 rounded to a page *)
  KV 0x7f000200 0x91aec;   (* SYMBOL: symbol vsnprintf+0x0 (plain size 204, asan size 204) *)
  KV 0x7f000300 0x91bb8;   (* SYMBOL: symbol sn_write+0x0 (plain size 220, asan size 220) *)
  KV 0x7f000400 0x8e9c0;   (* SYMBOL: symbol vfprintf+0x0 (plain size 432, asan size 432) *)
  KV 0x7f000700 0x8e070;   (* SYMBOL: symbol __lockfile+0x0 (plain size 252, asan size 252) *)
  KV 0x7f000800 0x8e16c].   (* SYMBOL: symbol __unlockfile+0x0 (plain size 96, asan size 96) *)

Definition A_iv : list (Z * Z * Z) := [
  KV3 0x109cc 0x10b9c (71348);   (* states *)
  KV3 0x10b9c 0x10bac (71348);   (* xdigits *)
  KV3 0x134a8 0x134f0 (445020);   (* emit_printf *)
  KV3 0x15f04 0x15f06 (468820);   (* __stack_chk_fail_local *)
  KV3 0x15f44 0x15f50 (468764);   (* __errno_location *)
  KV3 0x17d50 0x17e88 (485552);   (* __fwritex *)
  KV3 0x17f40 0x17f94 (485552);   (* __towrite *)
  KV3 0x18138 0x18234 (483128);   (* __lockfile *)
  KV3 0x18234 0x18294 (483128);   (* __unlockfile *)
  KV3 0x183bc 0x1854c (481984);   (* __stdio_write *)
  KV3 0x18554 0x18704 (484460);   (* vfprintf *)
  KV3 0x18704 0x19534 (484460);   (* printf_core *)
  KV3 0x19534 0x19668 (484460);   (* pop_arg *)
  KV3 0x19668 0x1973c (484460);   (* pad *)
  KV3 0x1973c 0x1ae04 (484460);   (* fmt_fp *)
  KV3 0x1ae04 0x1ae40 (448616);   (* strerror *)
  KV3 0x1ae48 0x1ae6c (468480);   (* wctomb *)
  KV3 0x1cfb4 0x1cfd0 (477980);   (* vprintf *)
  KV3 0x1d084 0x1d150 (477800);   (* vsnprintf *)
  KV3 0x1d150 0x1d22c (477800);   (* sn_write *)
  KV3 0x21334 0x21738 (462416);   (* memcpy *)
  KV3 0x21738 0x21830 (462416);   (* memset *)
  KV3 0x21920 0x21964 (463184);   (* strnlen *)
  KV3 0x23f60 0x24048 (497160);   (* __stdout_FILE *)
  KV3 0x34288 0x34290 (6028488)].   (* __stack_chk_guard *)

Definition A_sym (k : Z) : Z := tsym A_exact A_iv k.
Definition A_img : RImg := {| img_segs := A_segs; sym := A_sym |}.

(* THE SECOND INSTANCE.  GXA's G_vsnprintf.v uses `sym 0x7f000400` as vsnprintf's call target, and
   G_vfprintf_snf_closed.v uses the same symbol as musl vfprintf's body.  In an ASan image these are two
   objects: musl vsnprintf jumps to __interceptor_trampoline_vfprintf 0x41424 (its only jal to a vfprintf
   object), and the vfprintf interceptor and printf_common run before REAL(vfprintf) = musl vfprintf.  So
   vsnprintf is instantiated at A_img_vsn and the vfprintf body at A_img; the two agree on every other row. *)
Definition A_exact_vsn : list (Z * Z) := (0x7f000400, 0x41424) :: A_exact.
Definition A_sym_vsn (k : Z) : Z := tsym A_exact_vsn A_iv k.
Definition A_img_vsn : RImg := {| img_segs := A_segs; sym := A_sym_vsn |}.
Lemma A_sym_vsn_agree : forall k, k <> 0x7f000400 -> A_sym_vsn k = A_sym k.
Proof. intros k Hk. unfold A_sym_vsn, A_sym, tsym, A_exact_vsn. cbn [zlookup]. destruct (Z.eqb_spec k 0x7f000400); [contradiction | reflexivity]. Qed.

(* the rows that are still open, and why; none of them is a key RT_IImgA_ok.v checks *)
(* OPEN donor 0x10316 (3 uses): interval-end of [0x102e5,0x10316)-21 *)
(* OPEN donor 0x10352 (3 uses): unmapped *)
(* OPEN donor 0x17cec (3 uses): plain symbol fprintf has no asan counterpart *)
(* OPEN donor 0x182c4 (3 uses): interval-end of [0x18294,0x182c4)-6452 *)
(* OPEN donor 0x1d070 (3 uses): interval-end of [0x1cfd0,0x1d070)-25612 *)
(* OPEN donor 0x23e70 (3 uses): unmapped *)
(* OPEN donor 0x346e0 (3 uses): unmapped *)
