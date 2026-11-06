(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 87 of its 111 lines of code are new or changed and 494 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_KEYA (KEY 0x8661c -> KDISP 0x86714 or
   TAIL): the points inside the segment and their statements, in the form of m_file_m.v's MF_<cut>_stmt. The segment's code (the image-B m_file cut map section 4, S_MF_KEYA; listing
   the neutral listing of m_file in image B lines 315-388, 418-428):
     0x8661c  li a1,61; mv a0,s10; jal memchr (0x86624)        KEY: s10 = s = p + i, s4 = e = p + j, a2 = j - i
     0x86628  ld a1,136(s1); beqz a1 -> 0x867d4; beqz a0 -> 0x867d4    cur = NULL or no '=': 0x867d4 mv a0,s9;
              mv a1,s11; jal m_refuse 0x867dc (KB_JREF); 0x867e0 li s4,511; ld s10,152(s1); j TAIL
     0x86634  sd s10,208(s1); sd a0,200(s1); li a1,-1; beq a0,a1 -> trap 0x86e84 (eq + 1 wraps: killed, eq lies in
              the text); addi a0,a0,1; sd a0,192(s1); sd s4,184(s1); addi a0,s1,208; addi a1,s1,200
     KB_S1 0x86658  jal strip (&k, &ke)                          the key [i, i + ei) of the line
     0x8665c  addi a0,s1,192; addi a1,s1,184
     KB_S2 0x86664  jal strip (&v, &ve)                          the value [i + ei + 1, j)
     KB_Q 0x86668   the quotes: ve - v < 2 -> 0x866dc; trap 0x8667c (v = NULL); the check of *v (0x86688, slow path
              0x86c6c-0x86c74, error path 0x86ef8); *v is a single quote (39) or a double quote (34) else 0x866dc; trap
              0x866a8 (ve <u 2); the check
              of ve[-1] (0x866b8, slow path 0x86c78-0x86c80, error path 0x86efc / 0x86f00); ve[-1] = *v else
              0x866dc; trap 0x866cc (v = -1); v + 1 into 192(s1), ve - 1 into 184(s1)
              0x866dc  a1 = 200(s1) = ke, a0 = 208(s1) = k, a2 = 184(s1) = ve, a3 = 192(s1) = v
     KB_U 0x866ec   low.i's shadow bytes shadow(FB) + 8 .. + 11 := 0; s5 = ke - k; s10 = ve - v; shadow(FB) + 4 .. + 7
              := 0 (mf_core moves from MF_LOW_OFF to MF_LOW_ON); KDISP 0x86714 (a0 = k: ka0 = true)
   At KB_S1 .. KB_U the walk keeps the KEY facts (kb_ctx: cur = Some gi and the '=' at ei of the stripped line sl =
   slice i j L, L = mf_line rest, so the model is mk_disp of the stripped key and the unquoted stripped value) and
   the four scratch cells 208 / 200 / 192 / 184 (mf_slot); after a strip the key / value are index facts in the
   line's coordinates (kb_key_at / kb_val_at, from strip's post by mf_keya_m.v's kb_key_strip / kb_val_strip).
   A walk lane of the image-B m_file-family owner's G2B. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m mf_keya_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ============================ the points (listing offset = AF_m_file + (pc - 0x86140)) ============================ *)
Definition KB_RMC : Z := AF_m_file + 0x4e8.    (* 0x86628, memchr's return *)
Definition KB_JREF : Z := AF_m_file + 0x69c.   (* 0x867dc, jal m_refuse (cur = NULL or no '=') *)
Definition KB_S1 : Z := AF_m_file + 0x518.     (* 0x86658, jal strip (&k, &ke) *)
Definition KB_R1 : Z := AF_m_file + 0x51c.     (* 0x8665c, its return *)
Definition KB_S2 : Z := AF_m_file + 0x524.     (* 0x86664, jal strip (&v, &ve) *)
Definition KB_Q : Z := AF_m_file + 0x528.      (* 0x86668, its return: the quotes *)
Definition KB_U : Z := AF_m_file + 0x5ac.      (* 0x866ec, low.i marked usable *)

(* the key's stops in the line's coordinates: the stripped key h_strip (firstn ei sl) is [a, b) of L *)
Definition kb_key_at (L : list Z) (i j ei a b : nat) : Prop :=
(i <= a)%nat /\ (a <= b)%nat /\ (b <= i + ei)%nat /\ h_strip (firstn ei (slice i j L)) = slice a b L.
(* the value's stops: the stripped value h_strip (skipn (S ei) sl) is [c, d) of L *)
Definition kb_val_at (L : list Z) (i j ei c d : nat) : Prop :=
(i + S ei <= c)%nat /\ (c <= d)%nat /\ (d <= j)%nat /\ h_strip (skipn (S ei) (slice i j L)) = slice c d L.

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
   the unquoted stripped value (mf_keya_m.v kb_model_disp), and the next line's address in 152(s1) *)
Definition kb_ctx (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei n : nat) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
(i < j)%nat /\ (j <= length (mf_line rest))%nat /\
memchr (slice i j (mf_line rest)) EQ = Some ei /\
mf_fin (mk_disp mcc gi (h_strip (firstn ei (slice i j (mf_line rest))))
  (h_unquote (h_strip (skipn (S ei) (slice i j (mf_line rest))))) (line + 1), Some gi) line rest = mf_final v /\
mf_np v memc Wc (mf_next p rest).

(* the registers every point of the segment keeps: the cut registers and s11 = line + 1 *)
Definition kb_regs (v : mfv) (lyc : alayout) (pos : Z) (regs1 : bvmap 5 word) (line : Z) : Prop :=
mf_regs_at B v lyc pos regs1 /\ getr regs1 27 = w64 (line + 1).

(* 0x867dc, jal m_refuse: a0 = c, a1 = line + 1; the line is done as the refusal (cur kept), the next line's address
   in 152(s1) (image A's KA_REF_stmt, m_file_s_keya_r.v, at image B's registers) *)
Definition KB_REF_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (m_refuse mcc (line + 1) false, cur) (line + 1) (lines (mf_rest rest))) = mf_final v ->
mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 (mv_c v) -> getr regs1 11 = w64 (line + 1) -> getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc KB_JREF.

(* 0x86628, memchr's return: a0 = res, the wrapper's answer over the stripped line sl = slice i j L (0 when it
   holds no '=', else the address of the first one); cur in 136(s1) (mf_cells), s10 = p + i, s4 = p + j, s11 =
   line + 1, the next line's address in 152(s1). The model is still m_key's, as MF_KEY_stmt states it with the
   stripped line *)
Definition KB_RMC_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j : nat)
  (res : Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(i < j)%nat -> (j <= length (mf_line rest))%nat ->
match memchr (slice i j (mf_line rest)) EQ with
| Some ei => res = p + Z.of_nat (i + ei)
| None => res = 0
end ->
mf_fin (m_key mcc cur (slice i j (mf_line rest)) (line + 1), cur) line rest = mf_final v ->
getr regs1 10 = w64 res -> getr regs1 26 = w64 (p + Z.of_nat i) -> getr regs1 20 = w64 (p + Z.of_nat j) ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc KB_RMC.

(* 0x86658, jal strip (&k, &ke): 208(s1) = p + i, 200(s1) = the '=' p + i + ei, 192(s1) = p + i + ei + 1,
   184(s1) = p + j; a0 = s1 + 208, a1 = s1 + 200 *)
Definition KB_S1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei : nat),
kb_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> kb_regs v lyc pos regs1 line ->
mf_slot v memc Wc 208 (p + Z.of_nat i) -> mf_slot v memc Wc 200 (p + Z.of_nat (i + ei)) ->
mf_slot v memc Wc 192 (p + Z.of_nat (i + ei) + 1) -> mf_slot v memc Wc 184 (p + Z.of_nat j) ->
getr regs1 10 = w64 (mf_s1 (mv_sp v) + 208) -> getr regs1 11 = w64 (mf_s1 (mv_sp v) + 200) ->
mf_at B v Wc regs1 memc mdc KB_S1.

(* 0x86664, jal strip (&v, &ve): the key stripped to [a, b); 192(s1) = p + i + ei + 1, 184(s1) = p + j;
   a0 = s1 + 192, a1 = s1 + 184 *)
Definition KB_S2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b : nat),
kb_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> kb_regs v lyc pos regs1 line ->
kb_key_at (mf_line rest) i j ei a b ->
mf_slot v memc Wc 208 (p + Z.of_nat a) -> mf_slot v memc Wc 200 (p + Z.of_nat b) ->
mf_slot v memc Wc 192 (p + Z.of_nat (i + ei) + 1) -> mf_slot v memc Wc 184 (p + Z.of_nat j) ->
getr regs1 10 = w64 (mf_s1 (mv_sp v) + 192) -> getr regs1 11 = w64 (mf_s1 (mv_sp v) + 184) ->
mf_at B v Wc regs1 memc mdc KB_S2.

(* 0x86668, the second strip's return: the key is [a, b), the stripped value [c, d) *)
Definition KB_Q_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b c d : nat),
kb_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> kb_regs v lyc pos regs1 line ->
kb_key_at (mf_line rest) i j ei a b -> kb_val_at (mf_line rest) i j ei c d ->
mf_slot v memc Wc 208 (p + Z.of_nat a) -> mf_slot v memc Wc 200 (p + Z.of_nat b) ->
mf_slot v memc Wc 192 (p + Z.of_nat c) -> mf_slot v memc Wc 184 (p + Z.of_nat d) ->
mf_at B v Wc regs1 memc mdc KB_Q.

(* 0x866ec, after the quotes: the unquoted stripped value is [ov, ov + vl) of L; a0 = 208(s1) = p + a, a1 = p + b,
   a2 = p + ov + vl, a3 = 192(s1) = p + ov *)
Definition KB_U_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (i j ei a b ov vl : nat),
kb_ctx v lyc Sc Wc memc mdc pos mcc gi line p rest i j ei n -> kb_regs v lyc pos regs1 line ->
kb_key_at (mf_line rest) i j ei a b ->
(ov + vl <= length (mf_line rest))%nat ->
h_unquote (h_strip (skipn (S ei) (slice i j (mf_line rest)))) = slice ov (ov + vl) (mf_line rest) ->
mf_slot v memc Wc 208 (p + Z.of_nat a) -> mf_slot v memc Wc 192 (p + Z.of_nat ov) ->
getr regs1 10 = w64 (p + Z.of_nat a) -> getr regs1 11 = w64 (p + Z.of_nat b) ->
getr regs1 12 = w64 (p + Z.of_nat (ov + vl)) -> getr regs1 13 = w64 (p + Z.of_nat ov) ->
mf_at B v Wc regs1 memc mdc KB_U.

End e.
End f.
End d.
