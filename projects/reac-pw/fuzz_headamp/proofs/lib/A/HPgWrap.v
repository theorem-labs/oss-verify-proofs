(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem
   statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin image A from
   proofs/libreac/fuzz_identity/lib/A/Rt/StrlenDef.v (astrlen_realizes, the premise and post shape) and
   lib/Reusable/YG0d.v abcmp_realizes at origin/ossv/recipes 6ebe35ba632: the two wrappers reac_box_pin_parse
   calls, strcspn and strncmp, are STATED here in that shape so that the
   P4b wrapper provers prove exactly these texts. The result specifications are pin's own plain ones:
   cspn_len is restated from proofs/reac-pw/fuzz_pin/lib/Prog/strcspn_c.v:12-16 (that file Requires the plain
   image module lib/Img0.v, which an image-independent text may not Require) and strncmp_model is
   lib/Spec/StrFun.v:149-158 itself, which Requires no image module. rule 24 (reuse): no function is proved
   here. *)

(* This comment is reac-pw/fuzz_pin's lib/A/PPgWrap.v, unchanged: its addresses are fuzz_pin.asan's (image A) and fuzz_pin.asan-ubsan's (image B). IMAGE-INDEPENDENT: segs, the symbol record B and the entry address pc are parameters, so image B
   (fuzz_pin.asan-ubsan) instantiates the same two texts at its own trampolines. In both pinned images the
   trampolines are __interceptor_trampoline_strcspn 0x4191c -> ___interceptor_strcspn 0x42cb8 and
   __interceptor_trampoline_strncmp 0x41914 -> ___interceptor_strncmp 0x42400 (4-byte `j` each), and musl's
   strcspn is 0x91864 (image A) / 0x91970 (image B) and musl's strncmp 0x91a80 / 0x91b8c.

   WHAT THE WRAPPERS READ, and why each premise is here (measured over the pinned images; capstone 5.0.7):
   - strcspn(s, set): the wrapper runs musl strcspn, then checks that the bytes [s, s + r] and the set's own
     bytes and NUL are marked usable, where r is the result. The contract fixes the set at EXACTLY one byte,
     which is pin's use (the set is ":" and its NUL, at 0x20d80 in both images; the one call site is
     reac_box_pin_parse 0x80c84). With a set of one byte musl strcspn goes through __strchrnul, whose word
     loop reads the whole 8-byte word that holds the byte it stops at; that byte is at or before the string's
     NUL, so the clause on the string's NUL granule covers every byte the loop reads. The two other cases are
     left out on purpose: an EMPTY set makes musl call __strchrnul(s, 0), which calls the strlen wrapper
     2256 bytes below the strcspn wrapper's sp, outside the 2 * ESTACK window astrlen_realizes asks for; a
     set of two bytes or more makes musl build a bitmap and read the set twice. Pin makes neither call.
   - strncmp(a, b, n): the wrapper compares byte by byte up to the first index where the bytes differ or one
     of them is 0, or until n bytes are compared, checks both read ranges, and returns the sign of the
     difference. The walk uses only "the result is 0 exactly when the compared prefixes are equal", so the
     post states that; the premise asks for both C strings, which is what reac_box_pin_parse holds (the
     token, read-only, and the spec string, a heap block). It also asks that each string's length + 8
     bytes lie in the application memory range (`amem_range x (len + 8)`), the form
     libreac/fuzz_boxreg's strncmp contract (lib/A/Rt/StrncmpDef.v fm_cstr_ok) states, because the ported
     walk needs that range for every length the runtime's range check is asked about. Pin's two arguments
     meet it: a token in .rodata (0x20dc0 .. 0x211a0) and the spec string in the harness's heap block.
   Both wrappers use at most 2 * ESTACK bytes below sp (their own frames and the runtime's range check), and
   write nothing but that window: the post's memory clause.
   The runtime cells the two wrappers read, which the allocator relation's const cells fix (so no premise
   names them), measured over the pinned files (cell = value):
     image A: REAL(strcspn) 0x9ad70 = 0x91864, REAL(strncmp) 0x9ad60 = 0x91a80, the stack-guard GOT cell
              0x99cd8 = 0x5f45d8, the flags pointer 0x99040 = 0x133128;
     image B: REAL(strcspn) 0x9ae90 = 0x91970, REAL(strncmp) 0x9ae80 = 0x91b8c, the stack-guard GOT cell
              0x99df8 = 0x5f46d8, the flags pointer 0x99160 = 0x133228. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_pin/lib/A/PPgWrap.v at 90722657971 (the same text at
   ee62985a892, the one lib/A/HPgCSpec.v and lib/A/HPgCallsStr.v cite) for reac-pw/fuzz_headamp; module paths changed;
   only the strncmp half is kept (awrap_str, awrap_post, astrncmp_realizes, word for word): headamp calls no strcspn,
   so cspn_len and astrcspn_realizes are left out, and aro_unowned_of_arodataP is left out because this unit's
   lib/A/Rt/WrapRo.v states the same lemma (aro_unowned_of_arodata) over lib/A/HPgBase.v's arodata_okP; no numeral
   of the text moves (the comment above is pin's, verbatim, and names fuzz_pin's addresses). *)
(* reac-pw/fuzz_headamp, both ASan images (fuzz_headamp.asan f3e0669d2819, fuzz_headamp.asan-ubsan 53edda9bdeeb;
   addresses measured on the unstripped twins b5f352154c54 / 1674e30a0698, whose loaded bytes are the pins'):
   __interceptor_trampoline_strncmp 0x41ba4 / 0x41c24 -> ___interceptor_strncmp 0x4268c / 0x4270c (4-byte `j`),
   musl strncmp 0x95c00 / 0x96078. The wrapper code is level-3 identical to pin's, hostd's and boxreg's (elfdis
   6edf458084a6: 374 insns). The cells it reads, which AR's const cells fix (lib/A/AF0m.v Tfib_const_abs, image A):
   REAL(strncmp) 0x9e080 = 0x95c00, the stack-guard GOT cell 0x9cff8 = 0x5f7d90, the flags pointer 0x9c360 =
   0x1368e8, the flag byte 0x1369dd = 0, asan_inited 0xa5a98, the shadow base cell 0x9c370 = 0xa4db8; image B: the
   GOT cells 0x9d478 = 0x5f8210 and 0x9c7e0 = 0x136d68, REAL(strncmp) 0x9e500.
   Callers (image A): LLVMFuzzerTestOneInput 0x83190 (the key test, a2 = 13) and reac_headamp_prop_parse_result
   0x849c8 (a2 = 13); each passes a C string and the literal "reac.headamp." (0x20f00 / 0x21460). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* A C string at x whose bytes are l, in the shape the two wrappers read it. *)
Definition awrap_str (W : world segs) (mem : word -> option byte) (regs : bvmap 5 word) (x : Z) (l : list byte) : Prop :=
0 < x /\ ~ In (Z_to_bv 8 0) l /\
Z.of_nat (length l) + 1 < 2 ^ 32 /\ x + Z.of_nat (length l) + 1 <= 2 ^ 63 /\
garr8 segs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) l ++ [0]) /\
src_ok segs W regs mem x (Z.of_nat (length l) + 1) /\
(forall a, x <= a <= x + Z.of_nat (length l) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
amem_range x (Z.of_nat (length l) + 1) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length l) + 1) /\
shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length l) + 1) /\
(forall a, x + Z.of_nat (length l) < a < x + Z.of_nat (length l) - (x + Z.of_nat (length l)) mod 8 + 8 ->
 aview segs (w_H W) mem a <> None).

(* The common post, in the shape fuzz_identity's lib/A/Rt/StrlenDef.v:49-54 states it: the allocator
   relation is kept, the callee-saved registers, gp, tp and sp come back, the model changes only by
   materialization (`same_but_materialized md md'`, which the caller's journal needs: lib/Reusable/YCbq.v
   ajournal_after_write asks for it), and no byte outside [sp - 2 * ESTACK, sp) changes. *)
Definition awrap_post (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (R : bvmap 5 word -> Prop) : world segs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\ R regs' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
 aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* ================================= the strncmp wrapper ================================= *)
Definition astrncmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y n (ls rs : list byte) (d : Z),
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
(forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 32 ->
awrap_str W mem regs x ls -> awrap_str W mem regs y rs ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
aro_unowned segs B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(awrap_post ly S W regs mem md (fun regs' => exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0))).
End c.
End b.
