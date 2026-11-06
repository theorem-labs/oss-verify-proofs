(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 101 of its 126 lines of code are new or changed and 493 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KEYA (KEY 0x8633c -> KDISP 0x86684 or TAIL): the points
   inside the segment and their statements, in the form of m_file_m.v's MF_<cut>_stmt (the m_file cut-statement lane). The
   segment's code (guide/MF-CUTS-A.md section 4, S_MF_KEYA; listing dis/m_file.fuzz_segconf.asan.s):
     0x8633c  li a1,61; mv a0,s11; jal memchr (s, '=', e - s)       KEY: s11 = s = p + i, s7 = e = p + j, a2 = j - i
     0x86348  ld a1,136(s1); beqz a1 -> 0x863a4; beqz a0 -> 0x863a4  cur = NULL or no '=': m_refuse(c, line + 1) 0x863ac,
                                                                    `j 0x86bdc` (`ld a7,144(s1)`, TAIL)
     0x86354  bgeu s11,a0 -> J1; a2 := a0; a1 := s11                 the key [i, i + ei) of the line
     L1 0x86364  the key's front strip (check of *a1, load *s11, blank test, s11++ / a1++, `bne s11,a0`); all blank:
                 0x86430 s11 := a2 (= the '=')
     J1 0x86434  bgeu s11,a0 -> 0x86484 (a2 := a0) -> J2; a1 := a0 - 1; a2 := a0
     L2 0x86440  the key's back strip (check of *a1, load a2[-1], blank test, a1--, a2--, `bltu s11,a3`); none left:
                 0x8654c a2 := s11
     J2 0x86550  s5 := a0 + 1; bgeu s5,s7 -> J3; a0 := a0 + 1
     L3 0x8655c  the value's front strip (check of *a0, load *s5, s5++ / a0++, `bne s5,s7`); all blank: 0x8659c s5 := s7
     J3 0x865a0  bgeu s5,s7 -> J4; a0 := s7 - 1
     L4 0x865a8  the value's back strip (check of *a0, load s7[-1], a0--, s7--, `bltu s5,a1`); none left: s7 := s5
     J4 0x865f0  the quotes (vl >= 2, checks of v[0] and v[vl-1]), s8 := line + 1, s6 := kl, s4 := vl, low.i's 8
                 shadow bytes := 0 (0x86664-0x86680), KDISP 0x86684
   At L1 .. J4 the walk keeps the KEY facts (ka_ctx: cur = Some gi and the '=' at ei of the stripped line, so the
   model is mk_disp of the key and value) and the stops of the loops as index facts in the line's coordinates; the
   key and value become SegModel's terms by m_file_s_keya_m.v's ka_key_idx / ka_val_idx / ka_unquote_idx at J4.
   The KEYA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_keya_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ============================ the points (listing offset = AF_m_file + (pc - 0x85ebc)) ============================ *)
Definition KA_RMC : Z := AF_m_file + 0x48c.    (* 0x86348, memchr's return *)
Definition KA_JREF : Z := AF_m_file + 0x4f0.   (* 0x863ac, jal m_refuse (cur = NULL or no '=') *)
Definition KA_RREF : Z := AF_m_file + 0x4f4.   (* 0x863b0, m_refuse's return: `j 0x86bdc` *)
Definition KA_L1 : Z := AF_m_file + 0x4a8.     (* 0x86364, the key's front strip *)
Definition KA_J1 : Z := AF_m_file + 0x578.     (* 0x86434, after it *)
Definition KA_L2 : Z := AF_m_file + 0x584.     (* 0x86440, the key's back strip *)
Definition KA_J2 : Z := AF_m_file + 0x694.     (* 0x86550, after it: the key is [a, b) *)
Definition KA_L3 : Z := AF_m_file + 0x6a0.     (* 0x8655c, the value's front strip *)
Definition KA_J3 : Z := AF_m_file + 0x6e4.     (* 0x865a0, after it *)
Definition KA_L4 : Z := AF_m_file + 0x6ec.     (* 0x865a8, the value's back strip *)
Definition KA_J4 : Z := AF_m_file + 0x734.     (* 0x865f0, after it: the stripped value is [c, d) *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the KEY facts the segment keeps from the memchr call on: the cut's facts with cur = Some gi, the stripped line
   sl = slice i j L of the line L = mf_line rest, its first '=' at ei, the model as mk_disp of the stripped key and
   the unquoted stripped value (m_file_s_keya_m.v ka_model_disp), and the next line's address in 144(s1) *)
Definition ka_ctx (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei n : nat) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
(length (mf_line rest) < 512)%nat /\ (i < j)%nat /\ (j <= length (mf_line rest))%nat /\
slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) /\
memchr (slice i j (mf_line rest)) EQ = Some ei /\
mf_fin (mk_disp mcc gi (h_strip (firstn ei (slice i j (mf_line rest))))
  (h_unquote (h_strip (skipn (S ei) (slice i j (mf_line rest))))) (line + 1), Some gi) line rest = mf_final v /\
mf_np v memc Wc (mf_next p rest).

(* the registers every point of the segment keeps: the cut registers and s6 = line + 1 *)
Definition ka_regs (v : mfv) (lyc : alayout) (pos : Z) (regs1 : bvmap 5 word) (line : Z) : Prop :=
mf_regs_at B v lyc pos regs1 /\ getr regs1 22 = w64 (line + 1).

(* the stops of the key's loops: the front strip stopped at a (a non-blank, or the '=' at i + ei), the back strip
   at b (b - 1 a non-blank, or b = a) *)
Definition ka_key_at (L : list Z) (i ei a b : nat) : Prop :=
(i <= a <= b)%nat /\ (b <= i + ei)%nat /\
all_blank L i a /\ (a = (i + ei)%nat \/ blank (nth a L 0) = false) /\
all_blank L b (i + ei) /\ (b = a \/ blank (nth (b - 1) L 0) = false).
(* the stops of the value's front loop at c (a non-blank, or j) *)
Definition ka_vfront_at (L : list Z) (i j ei c : nat) : Prop :=
(i + S ei <= c <= j)%nat /\ all_blank L (i + S ei) c /\ (c = j \/ blank (nth c L 0) = false).

(* L1 0x86364: the front strip at q: s11 = a1 = p + q, a0 = a2 = p + i + ei (the '='), s7 = p + j *)
Definition KA_L1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei q : nat),
ka_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs v lyc pos regs1 line ->
(i <= q < i + ei)%nat -> all_blank (mf_line rest) i q ->
getr regs1 27 = w64 (p + Z.of_nat q) -> getr regs1 11 = w64 (p + Z.of_nat q) ->
getr regs1 10 = w64 (p + Z.of_nat (i + ei)) -> getr regs1 12 = w64 (p + Z.of_nat (i + ei)) ->
getr regs1 23 = w64 (p + Z.of_nat j) ->
mf_at B v Wc regs1 memc mdc KA_L1.

(* J1 0x86434: the front strip stopped at a: s11 = p + a, a0 = p + i + ei, s7 = p + j *)
Definition KA_J1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a : nat),
ka_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs v lyc pos regs1 line ->
(i <= a <= i + ei)%nat -> all_blank (mf_line rest) i a ->
(a = (i + ei)%nat \/ blank (nth a (mf_line rest) 0) = false) ->
getr regs1 27 = w64 (p + Z.of_nat a) -> getr regs1 10 = w64 (p + Z.of_nat (i + ei)) ->
getr regs1 23 = w64 (p + Z.of_nat j) ->
mf_at B v Wc regs1 memc mdc KA_J1.

(* L2 0x86440: the back strip at b (a < b): a2 = p + b, a1 = p + b - 1, s11 = p + a, a0 = p + i + ei, s7 = p + j *)
Definition KA_L2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b : nat),
ka_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs v lyc pos regs1 line ->
(i <= a < b)%nat -> (b <= i + ei)%nat -> all_blank (mf_line rest) i a ->
(a = (i + ei)%nat \/ blank (nth a (mf_line rest) 0) = false) -> all_blank (mf_line rest) b (i + ei) ->
getr regs1 12 = w64 (p + Z.of_nat b) -> getr regs1 11 = w64 (p + Z.of_nat b - 1) ->
getr regs1 27 = w64 (p + Z.of_nat a) -> getr regs1 10 = w64 (p + Z.of_nat (i + ei)) ->
getr regs1 23 = w64 (p + Z.of_nat j) ->
mf_at B v Wc regs1 memc mdc KA_L2.

(* J2 0x86550: the key is [a, b): a2 = p + b, s11 = p + a, a0 = p + i + ei, s7 = p + j *)
Definition KA_J2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b : nat),
ka_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs v lyc pos regs1 line ->
ka_key_at (mf_line rest) i ei a b ->
getr regs1 12 = w64 (p + Z.of_nat b) -> getr regs1 27 = w64 (p + Z.of_nat a) ->
getr regs1 10 = w64 (p + Z.of_nat (i + ei)) -> getr regs1 23 = w64 (p + Z.of_nat j) ->
mf_at B v Wc regs1 memc mdc KA_J2.

(* L3 0x8655c: the value's front strip at c: s5 = a0 = p + c, s7 = p + j; the key in a2 / s11 *)
Definition KA_L3_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b c : nat),
ka_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs v lyc pos regs1 line ->
ka_key_at (mf_line rest) i ei a b ->
(i + S ei <= c < j)%nat -> all_blank (mf_line rest) (i + S ei) c ->
getr regs1 21 = w64 (p + Z.of_nat c) -> getr regs1 10 = w64 (p + Z.of_nat c) ->
getr regs1 23 = w64 (p + Z.of_nat j) ->
getr regs1 12 = w64 (p + Z.of_nat b) -> getr regs1 27 = w64 (p + Z.of_nat a) ->
mf_at B v Wc regs1 memc mdc KA_L3.

(* J3 0x865a0: the value's front strip stopped at c: s5 = p + c, s7 = p + j *)
Definition KA_J3_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b c : nat),
ka_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs v lyc pos regs1 line ->
ka_key_at (mf_line rest) i ei a b -> ka_vfront_at (mf_line rest) i j ei c ->
getr regs1 21 = w64 (p + Z.of_nat c) -> getr regs1 23 = w64 (p + Z.of_nat j) ->
getr regs1 12 = w64 (p + Z.of_nat b) -> getr regs1 27 = w64 (p + Z.of_nat a) ->
mf_at B v Wc regs1 memc mdc KA_J3.

(* L4 0x865a8: the value's back strip at d (c < d): s7 = p + d, a0 = p + d - 1, s5 = p + c *)
Definition KA_L4_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b c d : nat),
ka_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs v lyc pos regs1 line ->
ka_key_at (mf_line rest) i ei a b -> ka_vfront_at (mf_line rest) i j ei c ->
(c < d <= j)%nat -> all_blank (mf_line rest) d j ->
getr regs1 23 = w64 (p + Z.of_nat d) -> getr regs1 10 = w64 (p + Z.of_nat d - 1) ->
getr regs1 21 = w64 (p + Z.of_nat c) ->
getr regs1 12 = w64 (p + Z.of_nat b) -> getr regs1 27 = w64 (p + Z.of_nat a) ->
mf_at B v Wc regs1 memc mdc KA_L4.

(* J4 0x865f0: the stripped value is [c, d): s5 = p + c, s7 = p + d *)
Definition KA_J4_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b c d : nat),
ka_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> ka_regs v lyc pos regs1 line ->
ka_key_at (mf_line rest) i ei a b -> ka_vfront_at (mf_line rest) i j ei c ->
(c <= d <= j)%nat -> all_blank (mf_line rest) d j -> (d = c \/ blank (nth (d - 1) (mf_line rest) 0) = false) ->
getr regs1 21 = w64 (p + Z.of_nat c) -> getr regs1 23 = w64 (p + Z.of_nat d) ->
getr regs1 12 = w64 (p + Z.of_nat b) -> getr regs1 27 = w64 (p + Z.of_nat a) ->
mf_at B v Wc regs1 memc mdc KA_J4.

End e.
End f.
End d.
