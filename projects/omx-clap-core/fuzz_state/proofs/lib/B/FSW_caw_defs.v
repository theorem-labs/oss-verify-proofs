(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 1279 of its 1357 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_K.v from a working branch
   60d0985773d, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_K.v; 95 of its 117 lines of code are new or changed and 1335 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_defs.v (a working branch
   83638d8ab68), the same names over B's own code. Every B literal below is from B's listing (capstone over the unstripped
   twin of fs.asan-ubsan, sha256 b1566a1c..., whose bytes 0x8164c .. 0x81b5c equal the pinned image's, sha256
   5ac5ce0954f8...) or from B's generated constants (lib/B/YB1w.v tfib_A_check_as_written / tfib_E_check_as_written,
   lib/B/FSH_Base.v A_check_as_written, FRAME_check_as_written = 64).
   rule 24: proves no function (kind: segment lemma; check_as_written, B 0x8164c, CONFIRM by a Theorem Labs lane). *)
(* Shared definitions of the check_as_written walk over fs.asan-ubsan (B 0x8164c, 324 instructions): the code table, the
   shadow-base span the token engine runs over, the stack frame, the canonical symbolic state of the scan loop of the
   inlined expected_body (fs.c:78-90) and the hand-over state of the empty-text arm. Definitions only.

   THE A -> B MAP (MEASURED: both listings, capstone; B's UBSan checks trap inline at 0x81ad4 `unimp`, no
   __ubsan_handle_* call):
     A 0x81590 (308 instr, frame 48, ra s0..s4 saved)       B 0x8164c (324 instr, frame 64, ra s0..s6 saved)
     strlen#1 / malloc#1 0x815c4 / 0x815d8                  0x81688 / 0x8169c
     strlen#2 / malloc#2 0x815e8 / 0x815f4                  0x816ac / 0x816b8
     t[0] shadow check 0x815fc, `beqz` empty 0x81610        0x816c0, `not a3, a0` 0x816d4, `beqz` empty 0x816d8
     scan loop head 0x8163c (classify)                      0x8170c (classify)
     advance 0x816ac (shadow of a1, s3++, next byte)        0x8177c (`beq s3, -1` UBSan trap, shadow of a1, s3++)
     '=' 0x816d0 (`addiw a4, a4, 1`)                        0x817a4 (`addiw a2, t3, 1; blt a2, t3` UBSan trap)
     store six[m] 0x816dc .. 0x81704                        0x817b8 .. 0x817e4 (`bltu a3, a4` UBSan trap first)
     scan exit 0x81724 (both exits; reloads *text)          two exits: NUL 0x81804, refused character 0x81a78
                                                              (straight to `jal __wrap_free` with s5 = SIZE_MAX)
     empty text 0x81730 -> 0x81738 (reload, shadow check)   0x81810 -> 0x81818 (literals only, no memory read)
     tail tests 0x81738 .. 0x817cc                          0x81804 .. 0x81894 (`bltu a3, m - 1` UBSan traps)
     emit loop head 0x817dc, exit 0x8197c                   head 0x818ac, exit 0x81a78
     free(six) 0x8197c, bcmp 0x819a4, tail free 0x819cc     0x81a78, 0x81aa0, 0x81ad0
   Registers: A's m / pad (a3 / a4) are B's a4 / t3; B keeps n in s5 (A s3) and ~six in a3 (A: none); B's s3 is the
   text pointer in the scan and scratch in the emit loop.
   The method is A's (FSW_caw_defs.v of lib/A): the token engine (Reusable/YCbn.v over YCbq.v, in U form FSW_K
   fsw_aj_run_to_tokU) for every ASan check, alias facts for the computed addresses, one-byte region chunks for the read
   values. B's UBSan traps (`bltu a3, x`, `bgeu s5, a5`, `beq s3, a7`, `beq a2, a7`, `blt a2, t3`) are decided by the
   engine from the atom facts: ~six (atom 30) and ~want (atom 29) lie in [2^64 - 1 - CAW_CEIL, 2^64 - 4097], every
   index below 2^22; ra is the atom 31 (a Theorem Labs lane ruling 2026-10-29); atoms 29 and 30 are the slots of the entry t4 / t5,
   which no state of this walk names after the first call, like ra's 31, so run_K and every agreement bound of the
   engine are unchanged and every re-key that keeps the atoms below 35 / 44 / 47 keeps them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the code of check_as_written: B/YB1w.v tfib_A_check_as_written = 0x8164c .. tfib_E_check_as_written = 0x81b5c,
   1,296 bytes; MEASURED: 324 four-byte instructions, no compressed one, so every instruction the walk executes is a
   table entry ---- *)
Definition caw_text_count : nat := Z.to_nat ((tfib_E_check_as_written - tfib_A_check_as_written) / 4).
Lemma caw_text_exact : Z.of_nat caw_text_count * 4 = tfib_E_check_as_written - tfib_A_check_as_written.
Proof. vm_compute. reflexivity. Qed.
Lemma caw_text_count_324 : caw_text_count = 324%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma caw_entry_B : A_check_as_written = tfib_A_check_as_written.
Proof. reflexivity. Qed.
Definition caw_tbl : ctable := Eval vm_compute in build_table tfibsegs A_check_as_written 324 TEmpty.
Lemma caw_tbl_ok : table_ok tfibsegs caw_tbl.
Proof.
assert (E : caw_tbl = build_table tfibsegs A_check_as_written 324 TEmpty) by (vm_cast_no_check (eq_refl caw_tbl)).
rewrite E. apply build_table_ok0. unfold A_check_as_written. lia.
Qed.
(* the first word, the scan head, the free call, the UBSan trap, the last word and nothing past the range, as B's
   listing gives them *)
Lemma caw_tbl_probe :
  clookup caw_tbl 0x8164c = Some 0xfc010113 /\ clookup caw_tbl 0x8170c = Some 0xfbf60f13 /\
  clookup caw_tbl 0x81a78 = Some 0xe68d10ef /\ clookup caw_tbl 0x81ad4 = Some 0xc0001073 /\
  clookup caw_tbl 0x81b58 = Some 0xe98d70ef /\ clookup caw_tbl 0x81b5c = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- the token engine's shadow base: atom 32 of the entry env (FSW_K fss0T), the span of the ASan shadow ---- *)
Definition caw_Bx : sv := SOff 32 0.
Definition caw_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the upper bound of every client pointer (YCbq.v asan_consts: alloc_ceiling <= 0x7fffff800000) *)
Definition CAW_CEIL : Z := 140737479966720.
Definition CAW_F : Z := 64.                       (* the frame of check_as_written (dis: addi sp, sp, -0x40) *)
Lemma caw_F_frame : CAW_F = FRAME_check_as_written.
Proof. reflexivity. Qed.
Definition CAW_WSMASK : Z := 4294977024.          (* 2^32 + 2^13 + 2^10 + 2^9, the whitespace mask of 0x816f4 .. 0x81700 *)
(* ~p for a client pointer p in [4096, CAW_CEIL] (`not a3, a0` at 0x816d4, `not a5, s2` at 0x81898) *)
Definition CAW_NLO : Z := 2 ^ 64 - 1 - CAW_CEIL.
Definition CAW_NHI : Z := 2 ^ 64 - 4097.
(* SIZE_MAX, the canonical literal the engine leaves for `addi x, zero, -1` *)
Definition CAW_M1 : Z := 18446744073709551615.

(* the stack frame as the prologue (0x8164c-0x8166c) leaves it: ra and s0..s6 saved *)
Definition caw_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0
    [YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

(* ---- loop 1, the scan loop (0x8170c .. 0x81800, head 0x8170c), fs.c:78-90 ----
   atoms: 30 NS = ~six, 31 RA, 33 six, 34 want, 35 P = text + j, 36 A = P + 1, 37 C = the current character,
   38 M = m (sextets so far), 39 PAD = pad, 40 Q = six + m, 41 N = the next character, 42-44 scratch (t4, t5, t6).
   registers: a0 = six, a1 = A, a2 = C, a3 = NS, a4 = M, a5 = 25, a6 = 61 ('='), a7 = SIZE_MAX, t0 = 9,
   t1 = the whitespace mask, t2 = 43 ('+'), t3 = PAD, s2 = want, s3 = P, s4 = the shadow base, s5 = SIZE_MAX (the
   answer n if the scan refuses), s6 the entry s6, s0 = l, s1 = body.
   ra is the ATOM 31 (a Theorem Labs lane ruling 2026-10-29: after `jal __wrap_malloc` no contract gives ra = the return
   address; no segment of this walk READS ra, the epilogue reloads it from the frame, caw_stk's chunk at -8 = the
   ENTRY ra, atom 1). *)
Definition caw_regs1 : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-64); SOff 3 0; SOff 4 0;
   SLit 9; SLit CAW_WSMASK; SLit 43;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SOff 36 0; SOff 37 0; SOff 30 0; SOff 38 0;
   SLit 25; SLit 61; SLit CAW_M1;
   SOff 34 0; SOff 35 0; SOff 32 0;
   SLit CAW_M1; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 39 0; SOff 42 0; SOff 43 0; SOff 44 0].
(* the next text byte (read at 0x81794 after `addi s3, s3, 1`) and the byte six[m] the iteration may write *)
Definition caw_txt1 : YP09.region :=
  YP09.mkRegion (Some 35%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 41 0))].
Definition caw_six1 : YP09.region := YP09.mkRegion (Some 40%nat) 0 1 0 1 [].
Definition caw_mem1 : smem := [caw_stk; caw_txt1; caw_six1].
(* the atom facts of the loop head; `cls` is the character class interval the case walks (the engine decides the
   classification branches from it). pad is at most 3145728 (pad <= j < |tb| <= PRESET_FILE_MAX_BYTES), so the UBSan
   test of `pad++` (0x817a8 `addiw a2, t3, 1; blt a2, t3`) never sees 2^31 - 1. *)
Definition caw_facts1 (clo chi : Z) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (30%nat, mkAF CAW_NLO CAW_NHI 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 CAW_CEIL 0);
           (34%nat, mkAF 4096 CAW_CEIL 0);
           (35%nat, mkAF 4096 CAW_CEIL 0);
           (36%nat, mkAF 4096 CAW_CEIL 0);
           (37%nat, mkAF clo chi 0);
           (38%nat, mkAF 0 3145728 0);
           (39%nat, mkAF 0 3145728 0);
           (40%nat, mkAF 4096 CAW_CEIL 0);
           (41%nat, mkAF 0 255 0)]
          []
          [(SAlu ALU_ADD (SOff 33 0) (SOff 38 0), SOff 40 0)].
Definition caw_ss1 (clo chi : Z) : sstate := mkSS 0x8170c caw_regs1 caw_mem1 None (caw_facts1 clo chi).
(* the shadow entries: the next text byte and the byte six[m]; both are discharged from the walk's range premises *)
Definition caw_SH1 : list shent := [mkSHE 35 1 2; mkSHE 40 0 1].
Definition caw_K1 : nat := Eval vm_compute in run_K 0 caw_Bx caw_SH1 (caw_ss1 0 255).

(* ---- the empty-text arm's hand-over (0x81810, reached by `beqz a2` at 0x816d8 when t[0] is the NUL) ----
   the registers the arm and the free call at 0x81a78 read: a0 = six (33), a3 = ~six (30), s2 = want (34), s4 the
   shadow base (32), s0 / s1 (12 / 11), sp; ra the atom 31; the registers the arm sets before reading them (a1, a4,
   s5) and the dead ones on the fresh atoms 35 .. 37 and 39 .. 50 (atom 38 is m, which the arm's exit state keeps in
   a4: no register of this state names it); the frame region; no other region (the arm reads no memory) *)
Definition caw_regs810 : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-64); SOff 3 0; SOff 4 0;
   SOff 35 0; SOff 36 0; SOff 37 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SOff 39 0; SOff 40 0; SOff 30 0; SOff 41 0;
   SOff 42 0; SOff 43 0; SOff 44 0;
   SOff 34 0; SOff 45 0; SOff 32 0;
   SOff 46 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0].
Definition caw_facts810 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (30%nat, mkAF CAW_NLO CAW_NHI 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 CAW_CEIL 0);
           (34%nat, mkAF 4096 CAW_CEIL 0)]
          [] [].
Definition caw_ss810 : sstate := mkSS 0x81810 caw_regs810 [caw_stk] None caw_facts810.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* one byte of the machine's own memory *)
Definition caw_at (W : world tfibsegs) (mem : word -> option byte) (a v : Z) : Prop :=
  val_mem tfibsegs (rdW W mem) a 1 v.
(* the bytes of a block, by index *)
Definition caw_bytes (W : world tfibsegs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  forall i, (i < length l)%nat -> caw_at W mem (p + Z.of_nat i) (nth i l 0).
End c.
