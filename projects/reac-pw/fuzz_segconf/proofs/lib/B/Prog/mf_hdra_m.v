(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 107 of its 132 lines of code are new or changed and 493 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_HDRA (HDR 0x864f4 -> HFIND 0x865c0 or
   TAIL 0x86820): the statements at the segment's own points and how they chain to m_file_m.v's S_MF_HDRA. Statement
   text and logic only; each point's walk is in lib/B/Prog/mf_hdra_<k>.v. A walk lane of the image-B m_file-family owner's G2B.
   The image-B counterpart of the image-A m_file-family lane's lib/A/Prog/m_file_s_hdra_m.v (commit 88d61b26fa90),
   with image B's points: image B calls strip and ieq, so the points are the calls' returns, not image A's strip
   loops.

   THE POINTS (B pc; listing offset AF_m_file + (pc - 0x86140); the neutral listing of m_file in image B,
   the image-B m_file cut map section 4 S_MF_HDRA, table 4.1). Over the HDR state (m_file_m.v MF_HDR_stmt): the stripped line
   sl = slice i j (mf_line rest), s = p + i, e = p + j, c in s9, line + 1 in s11, the next line's address in 152(s1).
     RMC   0x86500 (+0x3c0)  memchr's return (the call 0x864fc): a0 = s + k or 0; s10 = s, s4 = e, s5 = 0x20
     RS1   0x86534 (+0x3f4)  strip's return (the call 0x86530 over the cells 208 / 200 = [s + 1, close)): 208(s1) =
                             b = p + q1, 200(s1) = be = p + r1 (mf_hdra_t.v hda_q1 / hda_r1); s5 = 0x20
     RIEQ  0x86558 (+0x418)  ieq's return (the call 0x86554, ieq(b, 7, "segment")): a0 = ieq's answer; the cells
                             as at RS1; s5 = 0x20
     RS2   0x865a4 (+0x464)  strip's return (the call 0x865a0 over the cells 192 / 184 = [b + 7, be)): 192(s1) = nm =
                             p + q2, 184(s1) = ne = p + r2 (hda_q2 / hda_r2)
     REF   0x867c0 (+0x680)  the refusal of RMC / RS1 / RIEQ: `mv a0,s9; mv a1,s11; jal m_refuse` (0x867c8), cur =
                             NULL (0x867cc), `j 867e0`: s4 = 511, s10 = 152(s1), `j` TAIL
     REF3  0x86b40 (+0xa00)  the refusal of RS2 (the name is empty or >= 16): `jal m_refuse` (0x86b48), cur = NULL
                             (0x86b4c), `j 867e4` (s4 = 511 already, 0x865ac): s10 = 152(s1), `j` TAIL
   Every point keeps m_file_m.v's mf_regs_at (s3, s6 .. s9 are not written in the segment; the calls keep them) and
   s11 = line + 1. The UBSan trap branches 0x86508 (close = -1), 0x86518 (s = -1), 0x86568 (b + 7 <u 8) are in RMC's
   and RIEQ's walks, each refuted from the text's place (p + |rest| + 1 <= 2 ^ 47, mf_loop's sa_addr). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m mf_hdra_t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== the points ===================================== *)
Definition HDA_RMC : Z := AF_m_file + 0x3c0.    (* 0x86500, memchr's return *)
Definition HDA_RS1 : Z := AF_m_file + 0x3f4.    (* 0x86534, the first strip's return *)
Definition HDA_RIEQ : Z := AF_m_file + 0x418.   (* 0x86558, ieq's return *)
Definition HDA_RS2 : Z := AF_m_file + 0x464.    (* 0x865a4, the second strip's return *)
Definition HDA_REF : Z := AF_m_file + 0x680.    (* 0x867c0, the refusal of RMC / RS1 / RIEQ *)
Definition HDA_REF3 : Z := AF_m_file + 0xa00.   (* 0x86b40, the refusal of RS2 *)
(* the call sites inside the walks (the `jal`s) *)
Definition HDA_J_STRIP1 : Z := AF_m_file + 0x3f0.  (* 0x86530 *)
Definition HDA_J_IEQ : Z := AF_m_file + 0x414.     (* 0x86554 *)
Definition HDA_J_STRIP2 : Z := AF_m_file + 0x460.  (* 0x865a0 *)
Definition HDA_J_REF : Z := AF_m_file + 0x688.     (* 0x867c8 *)
Definition HDA_J_REF3 : Z := AF_m_file + 0xa08.    (* 0x86b48 *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the line's facts every point keeps: MF_HDR_stmt's premises, less its registers *)
Definition hda_line (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc /\ mf_cells v lyc pos memc Wc cur /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc cur line p rest /\
mf_np v memc Wc (mf_next p rest).

(* the header facts: the stripped line is [i, j) of the line, '[' first, and the line's model is m_header's *)
Definition hda_hdr (v : mfv) (mcc : mconf) (line : Z) (rest : list Z) (i j : nat) : Prop :=
(length (mf_line rest) < 512)%nat /\ (i < j)%nat /\ (j <= length (mf_line rest))%nat /\
hda_sl rest i j = h_strip (h_cut_comment (mf_line rest)) /\ nth i (mf_line rest) 0 = LBR /\
mf_fin (m_header mcc (hda_sl rest i j) (line + 1)) line rest = mf_final v.

(* ------------------------------------- the refusals ------------------------------------- *)
(* 0x867c0: s9 = c, s11 = line + 1; the line's model is the refusal *)
Definition HDA_REF_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
mf_fin (m_refuse mcc (line + 1) false, None) line rest = mf_final v ->
getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc HDA_REF.

(* 0x86b40: as REF, and s4 = 511 (the join 0x867e4 skips `li s4,511`) *)
Definition HDA_REF3_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
mf_fin (m_refuse mcc (line + 1) false, None) line rest = mf_final v ->
getr regs1 27 = w64 (line + 1) -> getr regs1 20 = w64 511 ->
mf_at B v Wc regs1 memc mdc HDA_REF3.

(* ------------------------------------- the calls' returns ------------------------------------- *)
(* 0x86500, memchr's return: k <= j - i is the wrapper's answer (first_byte), memchr sl ']' its model, a0 = s + k
   or 0; s10 = s, s4 = e, s5 = 0x20, s11 = line + 1 *)
Definition HDA_RMC_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j k : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
hda_hdr v mcc line rest i j ->
(k <= j - i)%nat ->
memchr (hda_sl rest i j) RBR = (if (k <? j - i)%nat then Some k else None) ->
getr regs1 10 = (if (k <? j - i)%nat then w64 (p + Z.of_nat (i + k)) else w64 0) ->
getr regs1 26 = w64 (p + Z.of_nat i) -> getr regs1 20 = w64 (p + Z.of_nat j) ->
getr regs1 21 = w64 0x20 -> getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc HDA_RMC.

(* 0x86534, the first strip's return: the close is sl's last byte; 208(s1) = b = p + q1, 200(s1) = be = p + r1 *)
Definition HDA_RS1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
hda_hdr v mcc line rest i j -> hda_close rest i j ->
mf_slot v memc Wc 208 (p + Z.of_nat (hda_q1 rest i j)) -> mf_slot v memc Wc 200 (p + Z.of_nat (hda_r1 rest i j)) ->
getr regs1 21 = w64 0x20 -> getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc HDA_RS1.

(* 0x86558, ieq's return: be - b >= 8; a0 = ieq of the header bytes' first 7 and "segment" *)
Definition HDA_RIEQ_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
hda_hdr v mcc line rest i j -> hda_close rest i j ->
(hda_q1 rest i j + 8 <= hda_r1 rest i j)%nat ->
mf_slot v memc Wc 208 (p + Z.of_nat (hda_q1 rest i j)) -> mf_slot v memc Wc 200 (p + Z.of_nat (hda_r1 rest i j)) ->
getr regs1 10 = w64 (seg_spec.b2z (ieq (slice (hda_q1 rest i j) (hda_q1 rest i j + 7) rest) S_segment)) ->
getr regs1 21 = w64 0x20 -> getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc HDA_RIEQ.

(* 0x865a4, the second strip's return: the header passed "segment" and its blank; 192(s1) = nm = p + q2,
   184(s1) = ne = p + r2 *)
Definition HDA_RS2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
hda_hdr v mcc line rest i j -> hda_close rest i j ->
(hda_q1 rest i j + 8 <= hda_r1 rest i j)%nat ->
ieq (slice (hda_q1 rest i j) (hda_q1 rest i j + 7) rest) S_segment = true ->
sp_tab (nth (hda_q1 rest i j + 7) rest 0) = true ->
mf_slot v memc Wc 192 (p + Z.of_nat (hda_q2 rest i j)) -> mf_slot v memc Wc 184 (p + Z.of_nat (hda_r2 rest i j)) ->
getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc HDA_RS2.
End e.
End f.
End d.

(* ============================ how the points chain to S_MF_HDRA ============================ *)
(* Each point's walk proves its statement at every FP state from the statements of the points it reaches (the
   refusals from MF_TAIL_F, RS2 from REF3 and MF_HFIND_F); the files mf_hdra_<k>.v prove those implications, this
   section composes them. *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Definition HDA_REF_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_REF_stmt (fx := fx0) B n.
Definition HDA_REF3_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_REF3_stmt (fx := fx0) B n.
Definition HDA_RMC_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_RMC_stmt (fx := fx0) B n.
Definition HDA_RS1_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_RS1_stmt (fx := fx0) B n.
Definition HDA_RIEQ_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_RIEQ_stmt (fx := fx0) B n.
Definition HDA_RS2_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_RS2_stmt (fx := fx0) B n.

(* the point walks, as the files prove them (each under the Section hypotheses there) *)
Definition HDA_PARTS : Prop :=
(forall n, MF_TAIL_F B n -> HDA_REF_F n) /\
(forall n, MF_TAIL_F B n -> HDA_REF3_F n) /\
(forall n, HDA_REF3_F n -> MF_HFIND_F B n -> HDA_RS2_F n) /\
(forall n, HDA_REF_F n -> HDA_RS2_F n -> HDA_RIEQ_F n) /\
(forall n, HDA_REF_F n -> HDA_RIEQ_F n -> HDA_RS1_F n) /\
(forall n, HDA_REF_F n -> HDA_RS1_F n -> HDA_RMC_F n) /\
(forall n, HDA_RMC_F n -> MF_HDR_F B n).

Lemma s_mf_hdra_of_parts : HDA_PARTS -> S_MF_HDRA B.
Proof.
intros (R1 & R3 & S2 & RI & S1 & RM & HD) n HT HH.
pose proof (R1 n HT) as HR1. pose proof (R3 n HT) as HR3.
pose proof (S2 n HR3 HH) as HS2. pose proof (RI n HR1 HS2) as HRI.
pose proof (S1 n HR1 HRI) as HS1. pose proof (RM n HR1 HS1) as HRM.
exact (HD n HRM).
Qed.
End i.
End h.
End g.
