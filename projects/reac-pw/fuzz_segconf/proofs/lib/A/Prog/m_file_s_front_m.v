(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 111 of its 136 lines of code are new or changed and 493 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_FRONT (lib/A/Prog/m_file_m.v: HEAD 0x860d0 -> LONG 0x86110,
   HDR 0x862cc, KEY 0x8633c or TAIL 0x86cf8; MF-CUTS-A.md section 4, 113 instructions): the program points the
   segment's walk is cut at, one FR_<point>_stmt each in the form of m_file_m.v's MF_<cut>_stmt (a state at
   BASE + pc whose registers and memory satisfy the point's predicate realizes the contract's post), and the logic
   that chains the pieces into MF_HEAD_stmt (S n). No instruction is executed here. The FRONT segment lane of the G2 walk owner's G2.

   THE POINTS (A pc; listing offset AF_m_file + (pc - 0x85ebc)), with what each adds to fr_ctx (the head's facts
   kept: mf_cx, mf_ls, mf_core at MF_LOW_OFF, mf_cells, mf_regs_at, s8 = FAKE, mf_loop, the head's model equation,
   s5 = c). L = |mf_line rest|, cut = h_cut_comment (mf_line rest), C = |cut|.
     SC 0x860dc (+0x220)  back from strchr(p, '\n'): a0 = fr_nl p rest (the '\n' or 0); s11 = p, s6 = line
     SL 0x860f0 (+0x234)  back from strlen(p), no '\n': a0 = |rest|, s4 = 0; s11 = p, s6 = line
     E  0x860f4 (+0x238)  s7 = p + L, s4 = fr_nl p rest; s11 = p, s6 = line
     from 0x86104 on (fr_short): s6 = line + 1, a7 = mf_next p rest, L < 512
     CL 0x8616c (+0x2b0)  the comment loop at i < L: a2 = a0 = p + i, a3 = -i, a6 = ';'; s11 = p, s7 = p + L;
                          no cut position before i
     CX 0x861fc (+0x340)  the cut: a2 = p + C; s11 = p
     SF 0x86208 (+0x34c)  the forward strip at k < C: s11 = a0 = p + k, s7 = p + C; cut[0, k) blank
     SM 0x8624c (+0x390)  the forward strip done at i0: s11 = p + i0, s7 = p + C
     SB 0x8625c (+0x3a0)  the backward strip at j: s7 = p + j, a0 = p + j - 1, s11 = a1 = p + i0; cut[j, C) blank
     ST 0x862a4 (+0x3e8)  the stripped line [i0, j0): s11 = p + i0, s7 = p + j0
   THE PIECES (each `<points it leaves to> -> <point it starts at>`): head (strchr), sc (the branch on a0, strlen),
   sl, e (line++, the long-line test, the empty line), cl (the comment loop, by induction), cx, sf (the forward
   strip, by induction), sm, sb (the backward strip, by induction), st (the check of *s, 144(s1), the '[' test). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_front_mdl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition FR_SC : Z := AF_m_file + 0x220.   (* 0x860dc, back from strchr *)
Definition FR_SL : Z := AF_m_file + 0x234.   (* 0x860f0, back from strlen *)
Definition FR_E : Z := AF_m_file + 0x238.    (* 0x860f4, the line's end known *)
Definition FR_CL : Z := AF_m_file + 0x2b0.   (* 0x8616c, the comment loop's head *)
Definition FR_CX : Z := AF_m_file + 0x340.   (* 0x861fc, the cut found *)
Definition FR_SF : Z := AF_m_file + 0x34c.   (* 0x86208, the forward strip's head *)
Definition FR_SM : Z := AF_m_file + 0x390.   (* 0x8624c, the forward strip done *)
Definition FR_SB : Z := AF_m_file + 0x3a0.   (* 0x8625c, the backward strip's head *)
Definition FR_ST : Z := AF_m_file + 0x3e8.   (* 0x862a4, the stripped line *)

(* the line with its comment cut, and its length *)
Definition fr_cut (rest : list Z) : list Z := h_cut_comment (mf_line rest).
Definition fr_C (rest : list Z) : nat := length (fr_cut rest).

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
mf_regs_at B v lyc pos regs1 /\ getr regs1 24 = w64 (frame_addr lyc 1 pos) /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc cur line p rest /\
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v /\ getr regs1 21 = w64 (mv_c v).

(* from 0x86104 on: s6 = line + 1, a7 = the next line's address, and the line is short (0x8610c not taken) *)
Definition fr_short (regs1 : bvmap 5 word) (line p : Z) (rest : list Z) : Prop :=
getr regs1 22 = w64 (line + 1) /\ getr regs1 17 = w64 (mf_next p rest) /\ (length (mf_line rest) < 512)%nat.

(* 0x860dc: back from strchr(p, '\n') *)
Definition FR_SC_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
getr regs1 27 = w64 p -> getr regs1 22 = w64 line -> getr regs1 10 = w64 (fr_nl p rest) ->
mf_at B v Wc regs1 memc mdc FR_SC.

(* 0x860f0: back from strlen(p) when the text left has no '\n' *)
Definition FR_SL_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
getr regs1 27 = w64 p -> getr regs1 22 = w64 line ->
existsb (fun b => b =? NL) rest = false -> getr regs1 20 = w64 0 ->
getr regs1 10 = w64 (Z.of_nat (length rest)) ->
mf_at B v Wc regs1 memc mdc FR_SL.

(* 0x860f4: s7 = the line's end, s4 = the '\n' or 0 *)
Definition FR_E_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
getr regs1 27 = w64 p -> getr regs1 22 = w64 line ->
getr regs1 23 = w64 (p + Z.of_nat (length (mf_line rest))) -> getr regs1 20 = w64 (fr_nl p rest) ->
mf_at B v Wc regs1 memc mdc FR_E.

(* 0x8616c: the comment loop at index i *)
Definition FR_CL_stmt (n i : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short regs1 line p rest ->
getr regs1 27 = w64 p -> getr regs1 23 = w64 (p + Z.of_nat (length (mf_line rest))) ->
getr regs1 16 = w64 59 ->
getr regs1 12 = w64 (p + Z.of_nat i) -> getr regs1 10 = w64 (p + Z.of_nat i) ->
getr regs1 13 = w64 (- Z.of_nat i) ->
(i < length (mf_line rest))%nat -> (forall k, (k < i)%nat -> cut_at (mf_line rest) k = false) ->
mf_at B v Wc regs1 memc mdc FR_CL.

(* 0x861fc: the comment cut is at C *)
Definition FR_CX_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short regs1 line p rest ->
getr regs1 27 = w64 p -> getr regs1 12 = w64 (p + Z.of_nat (fr_C rest)) ->
mf_at B v Wc regs1 memc mdc FR_CX.

(* 0x86208: the forward strip at k *)
Definition FR_SF_stmt (n k : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest,
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short regs1 line p rest ->
getr regs1 27 = w64 (p + Z.of_nat k) -> getr regs1 10 = w64 (p + Z.of_nat k) ->
getr regs1 23 = w64 (p + Z.of_nat (fr_C rest)) ->
(k < fr_C rest)%nat -> all_blank (fr_cut rest) 0 k ->
mf_at B v Wc regs1 memc mdc FR_SF.

(* 0x8624c: the forward strip stopped at i0 *)
Definition FR_SM_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest (i0 : nat),
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short regs1 line p rest ->
getr regs1 27 = w64 (p + Z.of_nat i0) -> getr regs1 23 = w64 (p + Z.of_nat (fr_C rest)) ->
(i0 <= fr_C rest)%nat -> all_blank (fr_cut rest) 0 i0 ->
(i0 = fr_C rest \/ blank (nth i0 (fr_cut rest) 0) = false) ->
mf_at B v Wc regs1 memc mdc FR_SM.

(* 0x8625c: the backward strip at j *)
Definition FR_SB_stmt (n j : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest (i0 : nat),
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short regs1 line p rest ->
getr regs1 27 = w64 (p + Z.of_nat i0) -> getr regs1 11 = w64 (p + Z.of_nat i0) ->
getr regs1 23 = w64 (p + Z.of_nat j) -> getr regs1 10 = w64 (p + Z.of_nat j - 1) ->
(i0 < j <= fr_C rest)%nat -> all_blank (fr_cut rest) 0 i0 -> blank (nth i0 (fr_cut rest) 0) = false ->
all_blank (fr_cut rest) j (fr_C rest) ->
mf_at B v Wc regs1 memc mdc FR_SB.

(* 0x862a4: the stripped line is the bytes [i0, j0) of the line *)
Definition FR_ST_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest (i0 j0 : nat),
fr_ctx v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short regs1 line p rest ->
getr regs1 27 = w64 (p + Z.of_nat i0) -> getr regs1 23 = w64 (p + Z.of_nat j0) ->
(i0 <= j0 <= length (mf_line rest))%nat -> slice i0 j0 (mf_line rest) = h_strip (fr_cut rest) ->
mf_at B v Wc regs1 memc mdc FR_ST.

(* the pieces chained: HEAD (S n) from the segment's exits at n *)
Lemma fr_chain : forall n,
  MF_TAIL_stmt B n ->
  MF_LONG_stmt B n ->
  MF_HDR_stmt B n ->
  MF_KEY_stmt B n ->
  (MF_TAIL_stmt B n ->
   MF_HDR_stmt B n ->
   MF_KEY_stmt B n -> FR_ST_stmt n) ->
  (FR_ST_stmt n -> forall j, FR_SB_stmt n j) ->
  ((forall j, FR_SB_stmt n j) -> FR_ST_stmt n -> FR_SM_stmt n) ->
  (FR_SM_stmt n -> forall k, FR_SF_stmt n k) ->
  ((forall k, FR_SF_stmt n k) -> FR_SM_stmt n -> FR_CX_stmt n) ->
  (FR_CX_stmt n -> forall i, FR_CL_stmt n i) ->
  (MF_LONG_stmt B n -> (forall i, FR_CL_stmt n i) -> FR_ST_stmt n ->
   FR_E_stmt n) ->
  (FR_E_stmt n -> FR_SL_stmt n) ->
  (FR_E_stmt n -> FR_SL_stmt n -> FR_SC_stmt n) ->
  (FR_SC_stmt n -> MF_HEAD_stmt B (S n)) ->
  MF_HEAD_stmt B (S n).
Proof.
intros n HT HL HH HK PST PSB PSM PSF PCX PCL PE PSL PSC PHD.
pose proof (PST HT HH HK) as ST. pose proof (PSB ST) as SB. pose proof (PSM SB ST) as SM.
pose proof (PSF SM) as SF. pose proof (PCX SF SM) as CX. pose proof (PCL CX) as CL.
pose proof (PE HL CL ST) as E. pose proof (PSL E) as SL. exact (PHD (PSC E SL)).
Qed.
End e.
End f.
End d.
