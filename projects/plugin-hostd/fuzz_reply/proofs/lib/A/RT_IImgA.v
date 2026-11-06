(* The RImg instance of the ASan printf core (lib/CJ/RL/GXA) on the pinned fuzz_reply.asan.
   GXA is general in the format (printf_core_a_stmt quantifies fmt and args) and proved (Qed,
   G_printf_core.v:1027 printf_core_a_proof, G_vfprintf_snf_closed.v:108 vfprintf_snf_a_closed),
   but it had no ASan instantiation in any unit on recipes.  This file is that instantiation.

   HOW EACH ROW WAS DECIDED (never by value, never by a uniform delta):
     SYMBOL   the donor address is carried to fuzz_reply.plain by the released IImgP map, and the
              plain address lies in a named symbol that the ASan image also has; the row keeps the
              offset inside the symbol.  The plain and ASan sizes agree on every one of these rows.
     CONTENT  the plain object's bytes occur exactly once in the ASan .rodata.
     CODEREF  the object is named by an auipc/addi pair inside a function of the chain in both images.
     GEOMETRY an image bound (the last PT_LOAD end, rounded to a page).
   Each row is checked again by the instance's own obligations (CodeAtT / RoB / RelCode by
   vm_compute against the image), so a wrong pairing cannot compile. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).

Definition A_exact : list (Z * Z) := [
  KV 0x1029e 0x10b54;   (* CONTENT: musl printf prefix "-+   0X0x", unique in asan .rodata on 10 bytes *)
  KV 0x102bf 0x147e0;   (* CONTENT: unique in asan .rodata on 24 bytes *)
  KV 0x102e5 0x15877;   (* CONTENT: unique in asan .rodata on 32 bytes *)
  KV 0x1032a 0x196f6;   (* CONTENT: unique in asan .rodata on 32 bytes *)
  KV 0x1034b 0x1d72f;   (* CONTENT: unique in asan .rodata on 32 bytes *)
  KV 0x10355 0x1d72f;   (* CONTENT: unique in asan .rodata on 32 bytes *)
  KV 0x1036a 0x1d744;   (* CONTENT: unique in asan .rodata on 16 bytes *)
  KV 0x103b3 0x2069f;   (* CONTENT: musl printf's "(null)" string (plain 0x103fe), unique in asan .rodata on its 7 bytes *)
  KV 0x10884 0x22158;   (* CODEREF: printf_core's jump table: named by the same auipc/addi pair inside printf_core in both images, a *)
  KV 0x10964 0x22238;   (* CODEREF: printf_core's second table (plain 0x10f20): named by an auipc/addi pair inside printf_core in bo *)
  KV 0x10984 0x22258;   (* CODEREF: pop_arg's jump table (plain 0x10f40): the only .rodata reference inside pop_arg in both images,  *)
  KV 0x109cc 0x222a0;   (* SYMBOL: symbol states+0x0 (plain size 464, asan size 464) *)
  KV 0x10b9c 0x22470;   (* SYMBOL: symbol xdigits+0x0 (plain size 16, asan size 16) *)
  KV 0x134a8 0x822a4;   (* SYMBOL: symbol emit_printf+0x0 (plain size 72, asan size 72) *)
  KV 0x15f04 0x8c9a0;   (* SYMBOL: symbol __stack_chk_fail_local+0x0 (plain size 8, asan size 8) *)
  KV 0x15f44 0x8c9a8;   (* SYMBOL: symbol __errno_location+0x0 (plain size 12, asan size 12) *)
  KV 0x17d50 0x92948;   (* SYMBOL: symbol __fwritex+0x0 (plain size 312, asan size 312) *)
  KV 0x17f40 0x92b38;   (* SYMBOL: symbol __towrite+0x0 (plain size 84, asan size 84) *)
  KV 0x183bc 0x921c4;   (* SYMBOL: symbol __stdio_write+0x0 (plain size 400, asan size 400) *)
  KV 0x18554 0x92d08;   (* SYMBOL: symbol vfprintf+0x0 (plain size 432, asan size 432) *)
  KV 0x18704 0x92eb8;   (* SYMBOL: symbol printf_core+0x0 (plain size 3632, asan size 3632) *)
  KV 0x19534 0x93ce8;   (* SYMBOL: symbol pop_arg+0x0 (plain size 308, asan size 308) *)
  KV 0x19668 0x93e1c;   (* SYMBOL: symbol pad+0x0 (plain size 212, asan size 212) *)
  KV 0x1973c 0x93ef0;   (* SYMBOL: symbol fmt_fp+0x0 (plain size 5832, asan size 5832) *)
  KV 0x1ae04 0x421ec;   (* CODEREF: jal target of strerror in printf_core: __interceptor_trampoline_strerror *)
  KV 0x1ae48 0x421e8;   (* CODEREF: jal target of wctomb in printf_core: __interceptor_trampoline_wctomb *)
  KV 0x1af98 0x8628c;   (* SYMBOL: __extenddftf2 (plain 0x1abd8, size 400 in both images) *)
  KV 0x1cfb4 0x95e18;   (* SYMBOL: symbol vprintf+0x0 (plain size 28, asan size 28) *)
  KV 0x1d084 0x95e34;   (* SYMBOL: symbol vsnprintf+0x0 (plain size 204, asan size 204) *)
  KV 0x1d150 0x95f00;   (* SYMBOL: symbol sn_write+0x0 (plain size 220, asan size 220) *)
  KV 0x21334 0x52724;   (* CODEREF: jal target of memcpy in sn_write and __fwritex: __interceptor_trampoline_memcpy *)
  KV 0x21738 0x52720;   (* CODEREF: jal target of memset in printf_core, pad and vsnprintf: __interceptor_trampoline_memset *)
  KV 0x21920 0x42190;   (* CODEREF: jal target of strnlen in printf_core: __interceptor_trampoline_strnlen *)
  KV 0x22e18 0x9e658;   (* CODEREF: the GOT word musl vsnprintf loads for the stack guard: auipc a2,0x9 / ld s2,-2044 at 0x95e54..0x *)
  KV 0x23f60 0xa2118;   (* SYMBOL: symbol __stdout_FILE+0x0 (plain size 232, asan size 232) *)
  KV 0x34288 0x5f94b0;   (* SYMBOL: symbol __stack_chk_guard+0x0 (plain size 8, asan size 8) *)
  KV 0x35000 0x5fb000;   (* GEOMETRY: last PT_LOAD end 0x5fad50 rounded to a page *)
  KV 0x7f000200 0x95e34;   (* SYMBOL: symbol vsnprintf+0x0 (plain size 204, asan size 204) *)
  KV 0x7f000300 0x95f00;   (* SYMBOL: symbol sn_write+0x0 (plain size 220, asan size 220) *)
  KV 0x7f000400 0x92d08;   (* SYMBOL: symbol vfprintf+0x0 (plain size 432, asan size 432) *)
  KV 0x7f000700 0x923b8;   (* SYMBOL: symbol __lockfile+0x0 (plain size 252, asan size 252) *)
  KV 0x7f000800 0x924b4].   (* SYMBOL: symbol __unlockfile+0x0 (plain size 96, asan size 96) *)

Definition A_iv : list (Z * Z * Z) := [
  KV3 0x109cc 0x10bac (71892);   (* states *)
  KV3 0x134a8 0x134f0 (454140);   (* emit_printf *)
  KV3 0x15f04 0x15f06 (486044);   (* __stack_chk_fail_local *)
  KV3 0x15f44 0x15f50 (485988);   (* __errno_location *)
  KV3 0x17d50 0x17e88 (502776);   (* __fwritex *)
  KV3 0x17f40 0x17f94 (502776);   (* __towrite *)
  KV3 0x18138 0x18234 (500352);   (* __lockfile *)
  KV3 0x18234 0x18294 (500352);   (* __unlockfile *)
  KV3 0x183bc 0x1854c (499208);   (* __stdio_write *)
  KV3 0x18554 0x18704 (501684);   (* vfprintf *)
  KV3 0x18704 0x19534 (501684);   (* printf_core *)
  KV3 0x19534 0x19668 (501684);   (* pop_arg *)
  KV3 0x19668 0x1973c (501684);   (* pad *)
  KV3 0x1973c 0x1ae04 (501684);   (* fmt_fp *)
  KV3 0x1ae04 0x1ae40 (465840);   (* strerror *)
  KV3 0x1ae48 0x1ae6c (485704);   (* wctomb *)
  KV3 0x1cfb4 0x1cfd0 (495204);   (* vprintf *)
  KV3 0x1d084 0x1d150 (495024);   (* vsnprintf *)
  KV3 0x1d150 0x1d22c (495024);   (* sn_write *)
  KV3 0x21334 0x21738 (479640);   (* memcpy *)
  KV3 0x21738 0x21830 (479688);   (* memset *)
  KV3 0x21920 0x21964 (480552);   (* strnlen *)
  KV3 0x34288 0x34290 (6050344)].   (* __stack_chk_guard *)

Definition A_sym (k : Z) : Z := tsym A_exact A_iv k.
Definition A_img : RImg := {| img_segs := tfibsegs; sym := A_sym |}.

(* THE SECOND INSTANCE.  GXA's G_vsnprintf.v:115 uses `sym 0x7f000400` as vsnprintf's call target, and
   G_vfprintf_snf_closed.v uses the same symbol as musl vfprintf's body.  In an ASan image these are two
   objects: musl vsnprintf jumps to __interceptor_trampoline_vfprintf 0x421d0 (measured, its jal at
   0x95ed0), and the vfprintf interceptor and printf_common run before REAL(vfprintf) = musl vfprintf
   0x92d08.  Both GXA sections are parametric in IMG, so vsnprintf is instantiated at A_img_vsn and the
   vfprintf body at A_img; the two agree on every other row, and the interceptor walk between them
   (Bz's I_vfprintfw with printf_common) is what glues vsnprintf's VF hypothesis to the closed body. *)
Definition A_exact_vsn : list (Z * Z) := (0x7f000400, 0x421d0) :: A_exact.
Definition A_sym_vsn (k : Z) : Z := tsym A_exact_vsn A_iv k.
Definition A_img_vsn : RImg := {| img_segs := tfibsegs; sym := A_sym_vsn |}.
Lemma A_sym_vsn_agree : forall k, k <> 0x7f000400 -> A_sym_vsn k = A_sym k.
Proof. intros k Hk. unfold A_sym_vsn, A_sym, tsym, A_exact_vsn. cbn [zlookup]. destruct (Z.eqb_spec k 0x7f000400); [contradiction | reflexivity]. Qed.

(* the rows that are still open, and why; none of them is on the %s / %d path *)
(* OPEN donor 0x102a8 (3 uses): interval-end of [0x1029e,0x102a8)-6 *)
(* OPEN donor 0x10316 (3 uses): interval-end of [0x102e5,0x10316)+7 *)
(* OPEN donor 0x10352 (3 uses): unmapped *)
(* OPEN donor 0x17cec (3 uses): plain symbol fprintf has no asan counterpart *)
(* OPEN donor 0x182c4 (3 uses): interval-end of [0x18294,0x182c4)-1028 *)
(* OPEN donor 0x1d070 (3 uses): interval-end of [0x1cfd0,0x1d070)-20120 *)
(* OPEN donor 0x23e70 (3 uses): unmapped *)
(* OPEN donor 0x346e0 (3 uses): unmapped *)
