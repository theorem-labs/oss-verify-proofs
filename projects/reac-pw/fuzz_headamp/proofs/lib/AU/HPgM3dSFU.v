(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): THE STATEMENTS of the five soft-float call adapters the image-B walk of the piece
   value_nearest of segment M03 of LLVMFuzzerTestOneInput (0x80c40) takes at its six soft-float calls. Statement
   text only: nothing is proved here. Proves no function (kind: segment lemma statement).

   THE SITES (the callees' entries are the twin's .symtab addresses; every return address is the `jal`'s pc + 4):
     0x835cc jal __extendsftf2 0x856c0, ra 0x835d0: the argument is the binary32 in fa0 (`fmv.s fa0,fs0` 0x835c8);
     0x83600 jal __getf2 0x85474 (= __gttf2), ra 0x83604: a0:a1 = d, a2:a3 = the binary128 -(2^63 + 1) of R+0xb8 /
             R+0xb0 (the pod.h:160 float-cast check; image B only);
     0x83610 jal __floatditf 0x8581c, ra 0x83614: a0 = s2 = fcvt.l.s of fs0;
     0x83624 jal __subtf3 0x85940, ra 0x83628: __subtf3 (16 bytes) runs into __addtf3 0x85950, whose 48-byte frame
             lies below sp;
     0x83638 jal __getf2 0x85474, ra 0x8363c: a2 = 0, a3 = R+0xa8, the 0.5L high word;
     0x83650 jal __lttf2 0x853ac (= __letf2 = __cmptf2 = __eqtf2 = __netf2, one routine), ra 0x83654: a2 = 0,
             a3 = R+0xa0, the -0.5L high word.
   The routines' sizes are image A's and fuzz_role's (348, 292, 16, 1996, 188, 200 bytes).

   WHAT EACH STATEMENT SAYS. hvu_sf_<routine>_stmt is the text of lib/A/HPgCallsSF.v's hc_sf_<routine>_call at image
   B's segments lib/AU/Img0U.v rsegs and image B's routine entry, with the return
   address a parameter (ret, with the range and parity lib/A/HPgCalls.v's hc_call asks) instead of image A's one
   fixed return address: image B calls __getf2 from two sites. From lib/A/HPgCalls.v's hc_core at the `jal`'s
   target, ra = ret, the argument registers, rom_view and a zero rounding mode, the walk continues at ret with
   hc_core at the returned state, the callee-saved registers, frames, blocks, I/O state and meter as at the call,
   every byte as at the call (for __subtf3: every byte outside [R - 48, R)), rom_view again, the routine's result
   in a0 (and a1) as its CJ post states it, and some float state fx2 with hd_fxk [] fx fx2 (every float register
   as at the call, a zero rounding mode).

   WHO PROVES THEM. The image-B twin of lib/A/HPgCallsSF.v (its lift needs image B's twin of lib/A/HPgSeamN.v)
   with the CJ contracts at an image-B RImg instance (the twin of lib/A/HPgCallsSFI.v). Until that file lands, the
   value_nearest walk takes each statement as a Section hypothesis of exactly this type. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YK0i YK1b YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module SF := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec.SoftFloat.

(* ======================================== image B: the routines ======================================== *)
Definition HVU_SF_EXT : Z := 0x856c0.     (* __extendsftf2 *)
Definition HVU_SF_FD : Z := 0x8581c.      (* __floatditf *)
Definition HVU_SF_SUB : Z := 0x85940.     (* __subtf3; runs into __addtf3 0x85950 *)
Definition HVU_SF_GE : Z := 0x85474.      (* __getf2 = __gttf2 *)
Definition HVU_SF_LT : Z := 0x853ac.      (* __lttf2 = __letf2 = __cmptf2 = __eqtf2 = __netf2 *)
(* the six return addresses of the value piece *)
Definition HVU_RA_EXT : Z := 0x835d0.
Definition HVU_RA_GT : Z := 0x83604.      (* the float-cast check's __gttf2 *)
Definition HVU_RA_FD : Z := 0x83614.
Definition HVU_RA_SUB : Z := 0x83628.
Definition HVU_RA_GE : Z := 0x8363c.
Definition HVU_RA_LT : Z := 0x83654.
(* __addtf3's frame below sp (G_subtf3.v addtf3_post: [sp - 48, sp)) *)
Definition HVU_SUB_STK : Z := 48.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* d = __extendsftf2(f), v = the 64-bit value of fa0 (the routine reads its low 32 bits); d in a0:a1 *)
Definition hvu_sf_ext_stmt : Prop :=
forall (ret : Z) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R v : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
bv_unsigned (reg_get (@fp_regs fx) 10) = v ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.lo64 (C_extendsftf2.f128_of_f32 v)) ->
 getr regs2 11 = w64 (SF.hi64 (C_extendsftf2.f128_of_f32 v)) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs HVU_SF_EXT regs memc mdc) Q.

(* __floatditf(t), t = a0 (any 64-bit two's-complement word); the binary128 value of t in a0:a1 *)
Definition hvu_sf_fd_stmt : Prop :=
forall (ret : Z) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R t : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
getr regs 10 = w64 t ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.lo64 (C_floatditf.f128_of_i64 t)) ->
 getr regs2 11 = w64 (SF.hi64 (C_floatditf.f128_of_i64 t)) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs HVU_SF_FD regs memc mdc) Q.

(* __subtf3(a, b), a = alo + 2^64 ahi in a0:a1, b = blo + 2^64 bhi in a2:a3; a - b in a0:a1; the callee (through
   __addtf3) writes its 48-byte frame [R - 48, R) and nothing else *)
Definition hvu_sf_sub_stmt : Prop :=
forall (ret : Z) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R alo ahi blo bhi : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
getr regs 10 = w64 alo -> getr regs 11 = w64 ahi -> getr regs 12 = w64 blo -> getr regs 13 = w64 bhi ->
0 <= alo < 2 ^ 64 -> 0 <= ahi < 2 ^ 64 -> 0 <= blo < 2 ^ 64 -> 0 <= bhi < 2 ^ 64 ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - HVU_SUB_STK <= x < R) ->
  aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.lo64 (SF.f128_sub (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi))) ->
 getr regs2 11 = w64 (SF.hi64 (SF.f128_sub (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi))) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs HVU_SF_SUB regs memc mdc) Q.

(* __getf2(a, b) = __gttf2(a, b), a in a0:a1, b in a2:a3; the comparison result (SoftFloat.f128_ge: 1 / 0 / -1,
   or -1 when unordered) in a0 *)
Definition hvu_sf_ge_stmt : Prop :=
forall (ret : Z) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R alo ahi blo bhi : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
getr regs 10 = w64 alo -> getr regs 11 = w64 ahi -> getr regs 12 = w64 blo -> getr regs 13 = w64 bhi ->
0 <= alo < 2 ^ 64 -> 0 <= ahi < 2 ^ 64 -> 0 <= blo < 2 ^ 64 -> 0 <= bhi < 2 ^ 64 ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.f128_ge (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs HVU_SF_GE regs memc mdc) Q.

(* __lttf2(a, b) (= __letf2's code), a in a0:a1, b in a2:a3; the comparison result (SoftFloat.f128_le: -1 / 0 / 1,
   or 1 when unordered) in a0 *)
Definition hvu_sf_lt_stmt : Prop :=
forall (ret : Z) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R alo ahi blo bhi : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
getr regs 10 = w64 alo -> getr regs 11 = w64 ahi -> getr regs 12 = w64 blo -> getr regs 13 = w64 bhi ->
0 <= alo < 2 ^ 64 -> 0 <= ahi < 2 ^ 64 -> 0 <= blo < 2 ^ 64 -> 0 <= bhi < 2 ^ 64 ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.f128_le (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs HVU_SF_LT regs memc mdc) Q.

(* the five together, as the value piece takes them *)
Definition hvu_sf_stmts : Prop :=
hvu_sf_ext_stmt /\ hvu_sf_fd_stmt /\ hvu_sf_sub_stmt /\ hvu_sf_ge_stmt /\ hvu_sf_lt_stmt.

End c.
End b.
