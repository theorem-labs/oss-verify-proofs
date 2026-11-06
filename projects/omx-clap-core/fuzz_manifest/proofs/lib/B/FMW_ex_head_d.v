(* G4.ExHead, IMAGE B: the scan head of expected (EX_L 0x813c0 .. EX_P / EX_NEXT / EX_R, fuzz_manifest.c:134-142) on
   fm.asan-ubsan (pin ca61e5c9eabc0050): the shared definitions of the head walk (symbolic states at its cuts, the
   shadow-token setup). Shape after image A's lib/A/FMW_ex_head_d.v (06d82004dc3); every pc, register and slot is B's
   (internal path).
   B keeps i in s7 (register 23) and text + i in s5 (register 21); the scan's constants are s0 = -1, s3 = 5, s11 = ' '
   (callee-saved) and a6 = text, a7 = 6, t0 = ':', t1 = the NUL/space mask (caller-saved, re-made after strncmp).
   Cuts inside the head:
     EX_L    0x813c0  text[i] (atom 32) at s5                                                     ss_L
     EX_W    0x81414  ex_prefix_word's loop head (inlined): the guard `bltu a3, a2`, a2 = k (k = 0..5),
                      a3 = ~(text + i), text[i + k] (atom 32), the shadow byte s of ex_prefix_word.word  ss_W k s
     EX_TL   0x81484  all six letters matched; text[i - 1] (atom 32, its byte region is added after the
                      i <> 0 test)                                                                ss_T
     EX_NEXT 0x81694  s7 = i + 1, s5 = text + s7, the guard `bgeu ~text, s7`, back to EX_L        ss_N
   s9 (register 25) holds the shadow base: the token base HD_Bx is register 25's atom. The literal registers s0, s3, s11,
   a7, t0, t1 are pinned. The facts on s5 (atom 21), s7 (atom 23), a3 (atom 13 at EX_W) and ~text (atom 32 at EX_NEXT)
   let the symbolic run decide the UBSan guards 0x813e4, 0x81414, 0x8148c, 0x814b4, 0x814c4 and 0x816a0 by their
   intervals (YP0e.v decide_cond2). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the cuts inside the head ---- *)
Definition EX_W : Z := 0x81414.    (* ex_prefix_word's loop head (inlined), a2 = k, fuzz_manifest.c:90-92 *)
Definition EX_TL : Z := 0x81484.   (* ex_prefix_word returned 1 (a2 = 6): the i == 0 / ex_space (p[-1]) test, :141 *)
Definition HD_WSH : Z := 0x41a4.   (* EX_WORD / 8: the offset of the word's shadow byte from the shadow base *)

(* ---- the shadow-token setup: s9 (register 25) holds the shadow base ---- *)
Definition HD_Bx : sv := SOff 25 0.
Definition HD_Bspan : Z * Z := EX_Bspan.

(* ---- the facts the head states carry ---- *)
Definition HD_AF2 : nat * afact := (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4).
Definition HD_AF25 : nat * afact := (25%nat, mkAF FW_SB FW_SB 0).
Definition HD_AF21 : nat * afact := (21%nat, mkAF 4096 (2 ^ 47 - 16) 0).        (* s5 = text + i *)
Definition HD_AF23 : nat * afact := (23%nat, mkAF 0 MANIFEST_MAX 0).            (* s7 = i *)
Definition HD_AF16 : nat * afact := (16%nat, mkAF 4096 (2 ^ 47 - 16) 0).        (* a6 = text *)
Definition HD_AFC : nat * afact := (32%nat, mkAF 0 255 0).                       (* atom 32: a text byte *)
Definition HD_AF13 : nat * afact := (13%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0).  (* EX_W: a3 = ~(text + i) *)
Definition HD_AFT : nat * afact := (32%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0).   (* EX_NEXT: atom 32 = ~text *)
(* s0 = -1, s3 = 5, s11 = ' ', a7 = 6, t0 = ':', t1 = the mask *)
Definition hd_pins (sr : list sv) : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr
    8%bv (SLit (2 ^ 64 - 1))) 19%bv (SLit 5)) 27%bv (SLit 32)) 17%bv (SLit 6)) 5%bv (SLit 58)) 6%bv (SLit EX_MASK1).

(* ---- EX_L: extra atom 32 = text[i] (the NUL when i = |t|); the frame slots the '@' path reads ---- *)
Definition hd_frameL : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x68 0x80 0x68 0x68
    [YP09.mkChunk 0x68 (CVal 8 (SLit EX_PREFIX)); YP09.mkChunk 0x70 (CVal 8 (SLit EX_MASK1));
     YP09.mkChunk 0x78 (CVal 8 (SOff 16 0))].
Definition hd_byteL : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_L : sstate :=
  mkSS EX_L (hd_pins sr_atoms) [hd_frameL; hd_byteL] None
    (mkFacts [HD_AF2; HD_AF25; HD_AF21; HD_AF23; HD_AF16; HD_AFC] [] []).
Definition SH_L : list shent := [mkSHE 21 0 1].
Definition hd_extraL (c : Z) : list word := [Z_to_bv 64 c].

(* ---- EX_W k s: a2 = k, a3 = register 13's atom = ~(text + i), extra atom 32 = text[i + k]; the word's shadow byte s
   (0 or 7: "prefix" has 7 addressable bytes in one granule) ---- *)
Definition hd_byteW (k : Z) : YP09.region :=
  YP09.mkRegion (Some 21%nat) k (k + 1) k k [YP09.mkChunk k (CVal 1 (SOff 32 0))].
Definition hd_wsh (s : Z) : YP09.region :=
  YP09.mkRegion (Some 25%nat) HD_WSH (HD_WSH + 1) HD_WSH HD_WSH [YP09.mkChunk HD_WSH (CVal 1 (SLit s))].
Definition ss_W (k s : Z) : sstate :=
  mkSS EX_W (sr_set (hd_pins sr_atoms) 12%bv (SLit k)) [hd_byteW k; hd_wsh s] None
    (mkFacts [HD_AF2; HD_AF25; HD_AF21; HD_AF23; HD_AF16; HD_AF13; HD_AFC] [] []).
Definition SH_W (k : Z) : list shent := [mkSHE 21 k (k + 1)].
(* the word byte k, which replaces the text byte region at 0x8144c (after the text byte is loaded) *)
Definition hd_wbyte (k : Z) : YP09.region :=
  YP09.mkRegion None (EX_WORD + k) (EX_WORD + k + 1) 0 0
    [YP09.mkChunk (EX_WORD + k) (CVal 1 (SLit (nth (Z.to_nat k) ManifestModel.prefix_lc 0)))].

(* ---- EX_TL: extra atom 32 = text[i - 1] (junk when i = 0: no region names it until the i <> 0 branch adds
   hd_byteT) ---- *)
Definition ss_T : sstate :=
  mkSS EX_TL (hd_pins sr_atoms) [] None
    (mkFacts [HD_AF2; HD_AF25; HD_AF21; HD_AF23; HD_AF16; HD_AFC] [] []).
Definition hd_byteT : YP09.region :=
  YP09.mkRegion (Some 21%nat) (-1) 0 (-1) (-1) [YP09.mkChunk (-1) (CVal 1 (SOff 32 0))].

(* ---- EX_NEXT: extra atom 32 = ~text, the slot F+0x80 ---- *)
Definition hd_frameN : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x80 0x88 0x80 0x80 [YP09.mkChunk 0x80 (CVal 8 (SOff 32 0))].
Definition ss_N : sstate :=
  mkSS EX_NEXT (hd_pins sr_atoms) [hd_frameN] None
    (mkFacts [HD_AF2; HD_AF25; HD_AF21; HD_AF23; HD_AF16; HD_AFT] [] []).

(* ---- the first arm of ManifestModel.head ('@' and "prefix" after it) ---- *)
Definition hd_arm1 (t : list Z) (i : nat) : bool :=
  (ManifestModel.byte_at t i =? 64) && ManifestModel.zl_eqb (firstn 6 (skipn (S i) t)) ManifestModel.prefix_lc.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* memory kept by the head's runs: everything but the strncmp call's stack window below F *)
Definition hd_keep (cx : ecx) (W3 : world tfibsegs) (mem1 mem2 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - STK_RT_STR <= a < cx_F cx) ->
    aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) mem1 a.
(* the journal from expected's entry to a state of the head *)
Definition hd_jr (cx : ecx) ly3 S3 (W3 : world tfibsegs) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem2 md2 0.
(* the registers the head keeps from its entry state regs1: sp, gp, tp, s9, s7 = i, s5 = text + i, a6 = text *)
Definition hd_kept_regs (regs1 regs2 : bvmap 5 word) : Prop :=
  getr regs2 2 = getr regs1 2 /\ getr regs2 3 = getr regs1 3 /\ getr regs2 4 = getr regs1 4 /\
  getr regs2 25 = getr regs1 25 /\ getr regs2 23 = getr regs1 23 /\ getr regs2 21 = getr regs1 21 /\
  getr regs2 16 = getr regs1 16.
(* the scan's literal registers (pinned at every cut): s0 = -1, s3 = 5, s11 = ' ', a7 = 6, t0 = ':', t1 = the mask *)
Definition hd_lits (regs2 : bvmap 5 word) : Prop :=
  getr regs2 8 = w64 (2 ^ 64 - 1) /\ getr regs2 19 = w64 5 /\ getr regs2 27 = w64 32 /\
  getr regs2 17 = w64 6 /\ getr regs2 5 = w64 58 /\ getr regs2 6 = w64 EX_MASK1.
End c.
