(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 80 of its 104 lines of code are new or changed and 494 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_FRONT of lib/B/Prog/m_file_m.v
   (HEAD 0x86378 -> LONG 0x863d4, HDR 0x864f4, KEY 0x8661c, TAIL 0x86820; the image-B m_file segment table section 2, the image-B m_file cut map
   section 4, 88 instructions): the program points the segment's walk is cut at, one FR_<point>_stmt each in the
   form of m_file_m.v's MF_<cut>_stmt (a state at BASE + pc whose registers and memory satisfy the point's predicate
   realizes the contract's post), and the logic that chains the pieces into MF_HEAD_stmt (S n). No instruction is
   executed here. A walk lane of the image-B m_file-family owner's G2B (on a working branch).
   ADAPTED from image A's lib/A/Prog/m_file_s_front_m.v (the image-A m_file-family lane, commit
   ae5120b8b0ec): the same head context fr_ctx and the same kind of points, at image B's code. Image B calls strip
   (image A inlines it), so A's forward / backward strip points SF / SM / SB are B's one strip call ST -> SR; image
   B keeps the line start and end in the frame cells 176(s1) / 168(s1) (strip's arguments), A in registers.

   THE POINTS (B pc; listing offset AF_m_file + (pc - 0x86140)). p = the text left's address, L = |mf_line rest|,
   C = fr_C rest (the comment cut's length), "slot o = x" = the 8-byte frame cell o(s1) holds x (m_file_m.v mf_slot).
   Every point keeps fr_ctx (the head's facts: mf_cx, mf_ls, sa_frm0, mf_core at MF_LOW_OFF, mf_cells, mf_regs_at,
   |rest| <= n, rest <> [], mf_loop, the head's model equation).
     SC 0x86384 (+0x244)  back from strchr(p, '\n') 0x86380: a0 = fr_nl p rest; s10 = p, s5 = line, s4 = 511
     SL 0x863ac (+0x26c)  back from strlen(p) 0x863a8 (no '\n'): a0 = |rest|; s10 = p, s5 = line, s4 = 511,
                          slot 176 = p
     E  0x863c4 (+0x284)  the line's end known: a0 = p + L, a2 = mf_next p rest, a6 = 0x20; s10 = p, s5 = line,
                          s4 = 511, slot 176 = p, slot 168 = p + L
     from 0x86420 on (fr_short): s11 = line + 1, s4 = 511, slot 152 = mf_next p rest (m_file_m.v mf_np), L < 512
     CL 0x86430 (+0x2f0)  the comment loop at index i < L: s10 = a1 = p + i, a3 = -i, a0 = p + L, a6 = 0x20,
                          slot 176 = p, slot 168 = p + L; no cut position before i
     ST 0x864b4 (+0x374)  the strip call's set-up: slot 176 = p, slot 168 = p + C
     SR 0x864c4 (+0x384)  back from strip(s1 + 176, s1 + 168) 0x864c0: slot 176 = p + i0, slot 168 = p + j0 with
                          slice i0 j0 (mf_line rest) = h_strip (fr_cut rest); s5 = 0x20
   THE PIECES (each `<points it leaves to> -> <point it starts at>`): hd (HEAD: the strchr call), sc (176(s1) = p, the
   branch on a0, the '\n' arm's 168(s1) store and its trap 0x86398, else the strlen call), sl (the trap 0x863b4,
   168(s1) = p + len), e (s11 = line + 1 and its trap 0x863c8, the long-line test 0x863d0 to LONG, 152(s1), the empty
   line 0x86424 to ST, else CL at 0), cl (one pass of the comment loop: the checks 0x86438 / 0x8646c, the trap
   0x8645c, the cut 0x864b0 to ST, else CL (S i) or the line's end to ST; by induction), st (the strip call), sr (the
   reloads, the empty stripped line 0x864cc to the join 0x867e0-0x867e8 and TAIL, the trap 0x864d0, the check
   0x864dc, the '[' test 0x864f0 to HDR or KEY). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m mf_front_mdl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition FR_SC : Z := AF_m_file + 0x244.   (* 0x86384, back from strchr *)
Definition FR_SL : Z := AF_m_file + 0x26c.   (* 0x863ac, back from strlen *)
Definition FR_E : Z := AF_m_file + 0x284.    (* 0x863c4, the line's end known *)
Definition FR_CL : Z := AF_m_file + 0x2f0.   (* 0x86430, the comment loop's head *)
Definition FR_ST : Z := AF_m_file + 0x374.   (* 0x864b4, the strip call's set-up *)
Definition FR_SR : Z := AF_m_file + 0x384.   (* 0x864c4, back from strip *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the head's facts every point of the segment keeps (MF_HEAD_stmt's, with |rest| <= n for HEAD (S n)) *)
Definition fr_ctx (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
(memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
(rest : list Z) (n : nat) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc /\ mf_cells v lyc pos memc Wc cur /\
mf_regs_at B v lyc pos regs1 /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc cur line p rest /\
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v.

(* from 0x86420 on: s11 = line + 1 (0x863c4), s4 = 511, 152(s1) = the next line's address (0x86420), the line short
   (0x863d0 taken) *)
Definition fr_short (v : mfv) (regs1 : bvmap 5 word) (memc : word -> option byte) (Wc : world SEGS) (line p : Z)
(rest : list Z) : Prop :=
getr regs1 27 = w64 (line + 1) /\ getr regs1 20 = w64 511 /\ mf_np v memc Wc (mf_next p rest) /\
(length (mf_line rest) < 512)%nat.

(* 0x86384: back from strchr(p, '\n') *)
Definition FR_SC_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
getr regs1 26 = w64 p -> getr regs1 21 = w64 line -> getr regs1 20 = w64 511 ->
getr regs1 10 = w64 (fr_nl p rest) ->
mf_at B v Wc regs1 memc mdc FR_SC.

(* 0x863ac: back from strlen(p) when the text left has no '\n' *)
Definition FR_SL_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
getr regs1 26 = w64 p -> getr regs1 21 = w64 line -> getr regs1 20 = w64 511 -> mf_slot v memc Wc 176 p ->
existsb (fun b => b =? NL) rest = false -> getr regs1 10 = w64 (Z.of_nat (length rest)) ->
mf_at B v Wc regs1 memc mdc FR_SL.

(* 0x863c4: a0 = the line's end, a2 = the next line's address, a6 = ' ' *)
Definition FR_E_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
getr regs1 26 = w64 p -> getr regs1 21 = w64 line -> getr regs1 20 = w64 511 -> mf_slot v memc Wc 176 p ->
mf_slot v memc Wc 168 (p + Z.of_nat (length (mf_line rest))) ->
getr regs1 10 = w64 (p + Z.of_nat (length (mf_line rest))) -> getr regs1 12 = w64 (mf_next p rest) ->
getr regs1 16 = w64 0x20 ->
mf_at B v Wc regs1 memc mdc FR_E.

(* 0x86430: the comment loop at index i (s10 = a1 = p + i, a3 = -i) *)
Definition FR_CL_stmt (n i : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short v regs1 memc Wc line p rest ->
mf_slot v memc Wc 176 p -> mf_slot v memc Wc 168 (p + Z.of_nat (length (mf_line rest))) ->
getr regs1 10 = w64 (p + Z.of_nat (length (mf_line rest))) -> getr regs1 16 = w64 0x20 ->
getr regs1 26 = w64 (p + Z.of_nat i) -> getr regs1 11 = w64 (p + Z.of_nat i) -> getr regs1 13 = w64 (- Z.of_nat i) ->
(i < length (mf_line rest))%nat -> (forall k, (k < i)%nat -> cut_at (mf_line rest) k = false) ->
mf_at B v Wc regs1 memc mdc FR_CL.

(* 0x864b4: the comment cut is at C; strip's two cells hold the cut line's ends *)
Definition FR_ST_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short v regs1 memc Wc line p rest ->
mf_slot v memc Wc 176 p -> mf_slot v memc Wc 168 (p + Z.of_nat (fr_C rest)) ->
mf_at B v Wc regs1 memc mdc FR_ST.

(* 0x864c4: back from strip, the stripped line is the bytes [i0, j0) of the line *)
Definition FR_SR_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest (i0 j0 : nat),
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short v regs1 memc Wc line p rest ->
getr regs1 21 = w64 0x20 ->
mf_slot v memc Wc 176 (p + Z.of_nat i0) -> mf_slot v memc Wc 168 (p + Z.of_nat j0) ->
(i0 <= j0 <= length (mf_line rest))%nat -> slice i0 j0 (mf_line rest) = h_strip (fr_cut rest) ->
mf_at B v Wc regs1 memc mdc FR_SR.

(* the pieces chained: HEAD (S n) from the segment's exits at n *)
Lemma fr_chain : forall n,
  MF_TAIL_stmt B n -> MF_LONG_stmt B n -> MF_HDR_stmt B n -> MF_KEY_stmt B n ->
  (MF_TAIL_stmt B n -> MF_HDR_stmt B n -> MF_KEY_stmt B n -> FR_SR_stmt n) ->
  (FR_SR_stmt n -> FR_ST_stmt n) ->
  (FR_ST_stmt n -> forall i, FR_CL_stmt n i) ->
  (MF_LONG_stmt B n -> FR_ST_stmt n -> (forall i, FR_CL_stmt n i) -> FR_E_stmt n) ->
  (FR_E_stmt n -> FR_SL_stmt n) ->
  (FR_E_stmt n -> FR_SL_stmt n -> FR_SC_stmt n) ->
  (FR_SC_stmt n -> MF_HEAD_stmt B (S n)) ->
  MF_HEAD_stmt B (S n).
Proof.
intros n HT HL HH HK PSR PST PCL PE PSL PSC PHD.
pose proof (PSR HT HH HK) as SR. pose proof (PST SR) as ST. pose proof (PCL ST) as CL.
pose proof (PE HL ST CL) as E. pose proof (PSL E) as SL. exact (PHD (PSC E SL)).
Qed.
End e.
End f.
End d.
