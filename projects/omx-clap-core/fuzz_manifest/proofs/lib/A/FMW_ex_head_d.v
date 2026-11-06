(* G4.ExHead: the scan head of expected (EX_L 0x81260 .. EX_P / EX_CONT / EX_R, fuzz_manifest.c:134-142) on fm.asan:
   the shared definitions of the head walk (symbolic states at its cuts, the shadow-token setup).
   Cuts inside the head:
     EX_L  0x81260  s4 = text + i (alias of s7 + s3, atom 32), text[i] (atom 33)            ss_L
     EX_W  0x812a4  ex_prefix_word's loop head, a2 = k (k = 0..5), s4 = atom 20 = text + i,
                    text[i + k] (atom 32), the shadow byte s of ex_prefix_word.word          ss_W k s
     EX_TL 0x81310  all six letters matched (a1 = 6); text[i - 1] (atom 32, its byte region
                    is added after the i <> 0 test)                                          ss_T
   s9 (register 25) holds the shadow base: the token base HD_Bx is register 25's atom. Registers 8, 9, 15, 16, 18, 22
   hold the scan's constants (' ', '@', ':', the NUL/space mask, 5, 6) and are pinned as literals. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the cuts inside the head ---- *)
Definition EX_W : Z := 0x812a4.    (* ex_prefix_word's loop head (inlined), a2 = k, fuzz_manifest.c:90-92 *)
Definition EX_TL : Z := 0x81310.   (* ex_prefix_word returned 1: a1 = 6, the i == 0 / ex_space (p[-1]) test, :141 *)
Definition HD_WSH : Z := 0x41a4.   (* EX_WORD / 8: the offset of the word's shadow byte from the shadow base *)

(* ---- the shadow-token setup: s9 (register 25) holds the shadow base ---- *)
Definition HD_Bx : sv := SOff 25 0.
Definition HD_Bspan : Z * Z := EX_Bspan.

(* ---- the facts every head state carries ---- *)
Definition HD_AF2 : nat * afact := (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4).
Definition HD_AF25 : nat * afact := (25%nat, mkAF FW_SB FW_SB 0).
(* s0 = ' ', s1 = '@', a5 = ':', a6 = the mask, s2 = 5, s6 = 6 *)
Definition hd_pins (sr : list sv) : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr
    8%bv (SLit 32)) 9%bv (SLit 64)) 15%bv (SLit 58)) 16%bv (SLit EX_MASK1)) 18%bv (SLit 5)) 22%bv (SLit 6).

(* ---- EX_L: extra atoms 32 = text + i, 33 = text[i] (the NUL when i = |t|) ---- *)
Definition hd_frameL : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x50 0x68 0x50 0x50
    [YP09.mkChunk 0x50 (CVal 8 (SLit EX_PREFIX)); YP09.mkChunk 0x60 (CVal 8 (SLit EX_MASK1))].
Definition hd_byteL : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition ss_L : sstate :=
  mkSS EX_L (hd_pins sr_atoms) [hd_frameL; hd_byteL] None
    (mkFacts [HD_AF2; HD_AF25; (32%nat, mkAF 4096 (2 ^ 47 - 16) 0); (33%nat, mkAF 0 255 0)] []
       [(SAlu ALU_ADD (SOff 23 0) (SOff 19 0), SOff 32 0)]).
Definition SH_L : list shent := [mkSHE 32 0 1].
Definition hd_extraL (t i c : Z) : list word := [Z_to_bv 64 (t + i); Z_to_bv 64 c].

(* ---- EX_W k s: a2 = k, s4 = register 20's atom = text + i, extra atom 32 = text[i + k]; the word's shadow byte s
   (0 or 7: "prefix" has 7 addressable bytes in one granule) ---- *)
Definition hd_byteW (k : Z) : YP09.region :=
  YP09.mkRegion (Some 20%nat) k (k + 1) k k [YP09.mkChunk k (CVal 1 (SOff 32 0))].
Definition hd_wsh (s : Z) : YP09.region :=
  YP09.mkRegion (Some 25%nat) HD_WSH (HD_WSH + 1) HD_WSH HD_WSH [YP09.mkChunk HD_WSH (CVal 1 (SLit s))].
Definition ss_W (k s : Z) : sstate :=
  mkSS EX_W (sr_set (hd_pins sr_atoms) 12%bv (SLit k)) [hd_byteW k; hd_wsh s] None
    (mkFacts [HD_AF2; HD_AF25; (20%nat, mkAF 4096 (2 ^ 47 - 16) 0); (32%nat, mkAF 0 255 0)] [] []).
Definition SH_W (k : Z) : list shent := [mkSHE 20 k (k + 1)].
(* the word byte k, which replaces the text byte region at 0x812d8 (after the text byte is loaded) *)
Definition hd_wbyte (k : Z) : YP09.region :=
  YP09.mkRegion None (EX_WORD + k) (EX_WORD + k + 1) 0 0
    [YP09.mkChunk (EX_WORD + k) (CVal 1 (SLit (nth (Z.to_nat k) ManifestModel.prefix_lc 0)))].

(* ---- EX_TL: s3 = register 19's atom = i, s4 = register 20's atom = text + i, extra atom 32 = text[i - 1] (junk when
   i = 0: no region names it until the i <> 0 branch adds hd_byteT) ---- *)
Definition ss_T : sstate :=
  mkSS EX_TL (hd_pins sr_atoms) [] None
    (mkFacts [HD_AF2; HD_AF25; (20%nat, mkAF 4096 (2 ^ 47 - 16) 0); (32%nat, mkAF 0 255 0)] [] []).
Definition hd_byteT : YP09.region :=
  YP09.mkRegion (Some 20%nat) (-1) 0 (-1) (-1) [YP09.mkChunk (-1) (CVal 1 (SOff 32 0))].

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
(* the registers the head keeps from its entry state regs1 *)
Definition hd_kept_regs (regs1 regs2 : bvmap 5 word) : Prop :=
  getr regs2 2 = getr regs1 2 /\ getr regs2 3 = getr regs1 3 /\ getr regs2 4 = getr regs1 4 /\
  getr regs2 25 = getr regs1 25 /\ getr regs2 23 = getr regs1 23 /\ getr regs2 22 = getr regs1 22 /\
  getr regs2 18 = getr regs1 18 /\ getr regs2 8 = getr regs1 8.
(* the scan's literal registers: s1 = '@', a5 = ':', a6 = the mask *)
Definition hd_lits (regs2 : bvmap 5 word) : Prop :=
  getr regs2 9 = w64 64 /\ getr regs2 15 = w64 58 /\ getr regs2 16 = w64 EX_MASK1.
End c.
