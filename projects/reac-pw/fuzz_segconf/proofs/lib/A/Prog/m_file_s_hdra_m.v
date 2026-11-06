(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 199 of its 225 lines of code are new or changed and 492 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA (HDR 0x862cc -> HFIND 0x86abc or TAIL 0x86cf8): the
   statements at the segment's own points and how they chain to S_MF_HDRA. Statement text and logic only; each
   point's walk is in lib/A/Prog/m_file_s_hdra_<k>.v. The HDRA segment lane of the G2 walk owner's G2.

   THE POINTS (A pc; listing offset AF_m_file + (pc - 0x85ebc); listing m_file.fuzz_segconf.asan.s, the G2 walk owner's
   guide/MF-CUTS-A.md section 4 S_MF_HDRA). Over the HDR state (m_file_m.v MF_HDR_stmt): the stripped line
   sl = slice i j (mf_line rest), s = p + i in s11 (never written in the segment), e = p + j, c, line + 1, the next
   line's address in 144(s1).
     REF1  0x86bcc (+0xd10)  refusal: `mv a0,s5; mv a1,s6; jal m_refuse` (0x86bd4), cur = NULL (0x86bd8), a7 = 144(s1)
                             (0x86bdc), to TAIL; entered from 0x862d8 (memchr: none), 0x862e4 (close + 1 <> e) and,
                             after `ld s5,128(s1)` at 0x86bc8, from 0x86aac / 0x86ab8 (the name is empty or >= 16)
     REF2  0x8652c (+0x670)  refusal: s5 = 128(s1), a1 = s6 = s7 = line + 1, `jal m_refuse` (0x8653c), cur = NULL,
                             s10 = 120(s1) (0x86544), a7 = 144(s1) (0x86bdc), to TAIL; entered from 0x8649c
                             (be - b < 8), 0x864b4 (ieq = 0), 0x864d8 (b[7] not '\t', not ' ')
     L1    0x862fc (+0x440)  the forward strip of [s + 1, close): s10 = a0 = the cursor s + q, a1 = s4 = close
     BK0   0x863e4 (+0x528)  its exit: s10 = s + q (the first non-blank of [s + 1, close), or close)
     L2    0x863ec (+0x530)  the backward strip: s4 = s + r, a0 = s4 - 1
     LEN   0x86490 (+0x5d4)  its exit: s4 = be = s + r; then be - b, ieq "segment" (0x864b0), b[7]
     L3    0x864ec (+0x630)  the forward strip of the name [b + 7, be): s5 = a0 = the cursor s + a, s4 = s6 = be,
                             s7 = line + 1, s10 = 120(s1) again (0x864e8)
     NB0   0x86a50 (+0xb94)  its exit: s5 = s + a
     L4    0x86a64 (+0xba8)  the backward strip of the name: s4 = s + z, a0 = s4 - 1, a1 = s5
     FIN   0x86aac (+0xbf0)  its exit: s4 = s + z; the name's checks, then HFIND (m_file_m.v MF_HFIND_stmt)
     RMC   0x862d8 (+0x41c)  memchr's return: a0 = s + k, k the first ']' of sl, or 0 when there is none
     RIEQ  0x864b4 (+0x5f8)  ieq's return: a0 = ieq(b[0 .. 7), "segment"), s6 = be - b, s7 = line + 1
   Indices are into sl: k the first ']' (memchr), q / r the header strip's ends, a / z the name strip's ends;
   m_file_s_hdra_t.v turns them into SegModel's m_header (hda_hdr_find, the hda_hdr_refuse_ lemmas).
   The registers every point keeps (hda_regs): m_file_m.v's mf_regs_at without s10, which the header strip
   borrows as its cursor (0x862e8-0x8648c), with s8 = FAKE, and s11 = s. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_hdra_t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== the points ===================================== *)
Definition HDA_REF1 : Z := AF_m_file + 0xd10.   (* 0x86bcc *)
Definition HDA_REF2 : Z := AF_m_file + 0x670.   (* 0x8652c *)
Definition HDA_L1 : Z := AF_m_file + 0x440.     (* 0x862fc *)
Definition HDA_BK0 : Z := AF_m_file + 0x528.    (* 0x863e4 *)
Definition HDA_L2 : Z := AF_m_file + 0x530.     (* 0x863ec *)
Definition HDA_LEN : Z := AF_m_file + 0x5d4.    (* 0x86490 *)
Definition HDA_L3 : Z := AF_m_file + 0x630.     (* 0x864ec *)
Definition HDA_NB0 : Z := AF_m_file + 0xb94.    (* 0x86a50 *)
Definition HDA_L4 : Z := AF_m_file + 0xba8.     (* 0x86a64 *)
Definition HDA_FIN : Z := AF_m_file + 0xbf0.    (* 0x86aac *)
Definition HDA_RMC : Z := AF_m_file + 0x41c.    (* 0x862d8, memchr's return *)
Definition HDA_RIEQ : Z := AF_m_file + 0x5f8.   (* 0x864b4, ieq's return *)

(* the stripped line *)
Definition hda_sl (rest : list Z) (i j : nat) : list Z := slice i j (mf_line rest).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the registers every point keeps: mf_regs_at without s10, s8 = FAKE *)
Definition hda_regs (v : mfv) (lyc : alayout) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (mv_sp v) /\ getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs1 18 = w64 SHADOW_OFF /\ getr regs1 19 = w64 0x20 /\ getr regs1 25 = w64 MF_BLANK /\
getr regs1 24 = w64 (frame_addr lyc 1 pos).

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

(* memchr's answer: ']' at k, the last byte of sl *)
Definition hda_close (rest : list Z) (i j k : nat) : Prop :=
memchr (hda_sl rest i j) RBR = Some k /\ S k = length (hda_sl rest i j).

(* the header bytes passed their checks *)
Definition hda_hok (rest : list Z) (i j k q r : nat) : Prop :=
hda_strip (hda_sl rest i j) 1 k q r /\ (q + 8 <= r)%nat /\
ieq (slice q (q + 7) (hda_sl rest i j)) S_segment = true /\ sp_tab (nth (q + 7) (hda_sl rest i j) 0) = true.

(* ------------------------------------- the refusals ------------------------------------- *)
(* 0x86bcc: s5 = c, s6 = line + 1, s10 = shadow(FB); the line's model is the refusal *)
Definition HDA_REF1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
mf_fin (m_refuse mcc (line + 1) false, None) line rest = mf_final v ->
getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc HDA_REF1.

(* 0x8652c: s7 = line + 1, s10 any; the line's model is the refusal *)
Definition HDA_REF2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> hda_regs v lyc pos regs1 ->
mf_fin (m_refuse mcc (line + 1) false, None) line rest = mf_final v ->
getr regs1 23 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc HDA_REF2.

(* ------------------------------------- the two calls' returns ------------------------------------- *)
(* 0x862d8, memchr's return: k <= |sl| is the wrapper's answer (first_byte), memchr sl ']' its model, a0 = s + k
   or 0; s5 = c, s6 = line + 1, s7 = e, s10 = shadow(FB) (not yet borrowed) *)
Definition HDA_RMC_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j k : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
hda_hdr v mcc line rest i j ->
(k <= length (hda_sl rest i j))%nat ->
memchr (hda_sl rest i j) RBR = (if (k <? length (hda_sl rest i j))%nat then Some k else None) ->
getr regs1 10 = (if (k <? length (hda_sl rest i j))%nat then w64 (p + Z.of_nat (i + k)) else w64 0) ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
getr regs1 23 = w64 (p + Z.of_nat j) ->
mf_at B v Wc regs1 memc mdc HDA_RMC.

(* 0x864b4, ieq's return: the header bytes hb = [q, r) of sl, be - b >= 8; a0 = ieq of hb's first 7 bytes and
   "segment"; s10 = b, s4 = be, s6 = be - b, s7 = line + 1 *)
Definition HDA_RIEQ_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z)
  (i j k q r : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> hda_regs v lyc pos regs1 ->
hda_hdr v mcc line rest i j -> hda_close rest i j k -> hda_strip (hda_sl rest i j) 1 k q r -> (q + 8 <= r)%nat ->
getr regs1 10 = w64 (seg_spec.b2z (ieq (slice q (q + 7) (hda_sl rest i j)) S_segment)) ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 23 = w64 (line + 1) ->
getr regs1 26 = w64 (p + Z.of_nat (i + q)) -> getr regs1 20 = w64 (p + Z.of_nat (i + r)) ->
getr regs1 22 = w64 (Z.of_nat (r - q)) ->
mf_at B v Wc regs1 memc mdc HDA_RIEQ.

(* ------------------------------------- the header strip ------------------------------------- *)
(* 0x862fc, the forward loop: the cursor s + q, 1 <= q < k, the bytes [1, q) blank *)
Definition HDA_L1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j k q : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> hda_regs v lyc pos regs1 ->
hda_hdr v mcc line rest i j -> hda_close rest i j k ->
(1 <= q < k)%nat -> hda_all_blank (hda_sl rest i j) 1 q ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
getr regs1 23 = w64 (p + Z.of_nat j) -> getr regs1 20 = w64 (p + Z.of_nat (i + k)) ->
getr regs1 26 = w64 (p + Z.of_nat (i + q)) -> getr regs1 10 = w64 (p + Z.of_nat (i + q)) ->
getr regs1 11 = w64 (p + Z.of_nat (i + k)) ->
mf_at B v Wc regs1 memc mdc HDA_L1.

(* 0x863e4, the forward loop's exit: s10 = s + q, q = k or sl[q] not blank *)
Definition HDA_BK0_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j k q : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> hda_regs v lyc pos regs1 ->
hda_hdr v mcc line rest i j -> hda_close rest i j k ->
(1 <= q <= k)%nat -> hda_all_blank (hda_sl rest i j) 1 q ->
(q = k \/ blank (nth q (hda_sl rest i j) 0) = false) ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
getr regs1 23 = w64 (p + Z.of_nat j) -> getr regs1 20 = w64 (p + Z.of_nat (i + k)) ->
getr regs1 26 = w64 (p + Z.of_nat (i + q)) ->
mf_at B v Wc regs1 memc mdc HDA_BK0.

(* 0x863ec, the backward loop: s4 = s + r, a0 = s4 - 1, q < r <= k, the bytes [r, k) blank *)
Definition HDA_L2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z)
  (i j k q r : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> hda_regs v lyc pos regs1 ->
hda_hdr v mcc line rest i j -> hda_close rest i j k ->
(1 <= q < r)%nat -> (r <= k)%nat -> hda_all_blank (hda_sl rest i j) 1 q ->
(q = k \/ blank (nth q (hda_sl rest i j) 0) = false) -> hda_all_blank (hda_sl rest i j) r k ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
getr regs1 26 = w64 (p + Z.of_nat (i + q)) -> getr regs1 20 = w64 (p + Z.of_nat (i + r)) ->
getr regs1 10 = w64 (p + Z.of_nat (i + r) - 1) ->
mf_at B v Wc regs1 memc mdc HDA_L2.

(* 0x86490, the header strip's end: b = s + q in s10, be = s + r in s4 *)
Definition HDA_LEN_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z)
  (i j k q r : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> hda_regs v lyc pos regs1 ->
hda_hdr v mcc line rest i j -> hda_close rest i j k -> hda_strip (hda_sl rest i j) 1 k q r ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 22 = w64 (line + 1) ->
getr regs1 26 = w64 (p + Z.of_nat (i + q)) -> getr regs1 20 = w64 (p + Z.of_nat (i + r)) ->
mf_at B v Wc regs1 memc mdc HDA_LEN.

(* ------------------------------------- the name strip ------------------------------------- *)
(* 0x864ec, the forward loop: s5 = a0 = the cursor s + a, q + 7 <= a < r, the bytes [q + 7, a) blank; s4 = s6 = be,
   s7 = line + 1, s10 = shadow(FB) *)
Definition HDA_L3_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z)
  (i j k q r a : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
hda_hdr v mcc line rest i j -> hda_close rest i j k -> hda_hok rest i j k q r ->
(q + 7 <= a < r)%nat -> hda_all_blank (hda_sl rest i j) (q + 7) a ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 23 = w64 (line + 1) ->
getr regs1 21 = w64 (p + Z.of_nat (i + a)) -> getr regs1 10 = w64 (p + Z.of_nat (i + a)) ->
getr regs1 20 = w64 (p + Z.of_nat (i + r)) -> getr regs1 22 = w64 (p + Z.of_nat (i + r)) ->
mf_at B v Wc regs1 memc mdc HDA_L3.

(* 0x86a50, its exit: s5 = s + a, a = r or sl[a] not blank *)
Definition HDA_NB0_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z)
  (i j k q r a : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
hda_hdr v mcc line rest i j -> hda_close rest i j k -> hda_hok rest i j k q r ->
(q + 7 <= a <= r)%nat -> hda_all_blank (hda_sl rest i j) (q + 7) a ->
(a = r \/ blank (nth a (hda_sl rest i j) 0) = false) ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 23 = w64 (line + 1) ->
getr regs1 21 = w64 (p + Z.of_nat (i + a)) -> getr regs1 20 = w64 (p + Z.of_nat (i + r)) ->
mf_at B v Wc regs1 memc mdc HDA_NB0.

(* 0x86a64, the backward loop: s4 = s + z, a0 = s4 - 1, a1 = s5 = s + a, a < z <= r, the bytes [z, r) blank;
   s6 = s7 = line + 1 *)
Definition HDA_L4_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z)
  (i j k q r a z : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
hda_hdr v mcc line rest i j -> hda_close rest i j k -> hda_hok rest i j k q r ->
(q + 7 <= a < z)%nat -> (z <= r)%nat -> hda_all_blank (hda_sl rest i j) (q + 7) a ->
(a = r \/ blank (nth a (hda_sl rest i j) 0) = false) -> hda_all_blank (hda_sl rest i j) z r ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 22 = w64 (line + 1) -> getr regs1 23 = w64 (line + 1) ->
getr regs1 21 = w64 (p + Z.of_nat (i + a)) -> getr regs1 11 = w64 (p + Z.of_nat (i + a)) ->
getr regs1 20 = w64 (p + Z.of_nat (i + z)) -> getr regs1 10 = w64 (p + Z.of_nat (i + z) - 1) ->
mf_at B v Wc regs1 memc mdc HDA_L4.

(* 0x86aac, the name strip's end: s5 = s + a, s4 = s + z *)
Definition HDA_FIN_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z)
  (i j k q r a z : nat),
hda_line n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
hda_hdr v mcc line rest i j -> hda_close rest i j k -> hda_hok rest i j k q r ->
hda_strip (hda_sl rest i j) (q + 7) r a z ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 22 = w64 (line + 1) -> getr regs1 23 = w64 (line + 1) ->
getr regs1 21 = w64 (p + Z.of_nat (i + a)) -> getr regs1 20 = w64 (p + Z.of_nat (i + z)) ->
mf_at B v Wc regs1 memc mdc HDA_FIN.
End e.
End f.
End d.

(* ============================ how the points chain to S_MF_HDRA ============================ *)
(* Each point's walk proves its statement at every FP state from the statements of the points it reaches (the
   refusals from MF_TAIL_F, FIN from REF1 and MF_HFIND_F, each loop by induction on the bytes left inside its own
   file). The proofs of those implications are the files m_file_s_hdra_<k>.v; this section only composes them. *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Definition HDA_REF1_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_REF1_stmt (fx := fx0) B n.
Definition HDA_REF2_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_REF2_stmt (fx := fx0) B n.
Definition HDA_L1_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_L1_stmt (fx := fx0) B n.
Definition HDA_BK0_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_BK0_stmt (fx := fx0) B n.
Definition HDA_L2_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_L2_stmt (fx := fx0) B n.
Definition HDA_LEN_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_LEN_stmt (fx := fx0) B n.
Definition HDA_L3_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_L3_stmt (fx := fx0) B n.
Definition HDA_NB0_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_NB0_stmt (fx := fx0) B n.
Definition HDA_L4_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_L4_stmt (fx := fx0) B n.
Definition HDA_FIN_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_FIN_stmt (fx := fx0) B n.
Definition HDA_RMC_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_RMC_stmt (fx := fx0) B n.
Definition HDA_RIEQ_F (n : nat) : Prop := forall fx0 : YK11.FPState, HDA_RIEQ_stmt (fx := fx0) B n.

(* the point walks, as the files prove them (each under the Section hypotheses there) *)
Definition HDA_PARTS : Prop :=
(forall n, MF_TAIL_F B n -> HDA_REF1_F n) /\
(forall n, MF_TAIL_F B n -> HDA_REF2_F n) /\
(forall n, HDA_REF1_F n -> MF_HFIND_F B n -> HDA_FIN_F n) /\
(forall n, HDA_FIN_F n -> HDA_L4_F n) /\
(forall n, HDA_FIN_F n -> HDA_L4_F n -> HDA_NB0_F n) /\
(forall n, HDA_NB0_F n -> HDA_L3_F n) /\
(forall n, HDA_REF2_F n -> HDA_L3_F n -> HDA_RIEQ_F n) /\
(forall n, HDA_REF2_F n -> HDA_RIEQ_F n -> HDA_LEN_F n) /\
(forall n, HDA_LEN_F n -> HDA_L2_F n) /\
(forall n, HDA_LEN_F n -> HDA_L2_F n -> HDA_BK0_F n) /\
(forall n, HDA_BK0_F n -> HDA_L1_F n) /\
(forall n, HDA_REF1_F n -> HDA_BK0_F n -> HDA_L1_F n -> HDA_RMC_F n) /\
(forall n, HDA_RMC_F n -> MF_HDR_F B n).

Lemma s_mf_hdra_of_parts : HDA_PARTS -> S_MF_HDRA B.
Proof.
intros (R1 & R2 & FN & L4 & NB & L3 & RI & LN & L2 & BK & L1 & RM & HD) n HT HH.
pose proof (R1 n HT) as HR1. pose proof (R2 n HT) as HR2.
pose proof (FN n HR1 HH) as HFN. pose proof (L4 n HFN) as HL4. pose proof (NB n HFN HL4) as HNB.
pose proof (L3 n HNB) as HL3. pose proof (RI n HR2 HL3) as HRI. pose proof (LN n HR2 HRI) as HLN.
pose proof (L2 n HLN) as HL2. pose proof (BK n HLN HL2) as HBK. pose proof (L1 n HBK) as HL1.
exact (HD n (RM n HR1 HBK HL1)).
Qed.
End i.
End h.
End g.
