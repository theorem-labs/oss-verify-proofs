(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1d0 X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X0bq X001.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1cn.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0.

Import ListNotations.
Open Scope Z_scope.

Section DrvF.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.

Definition STARTF (c : config) : Prop :=
exists (Σ : rts RT) (usp ap : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
ASTA RT Σ (PMfd fds0 fs)
(eq (entry_st (Z_to_bv 64 MAIN_RA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
(Z_to_bv 64 (Z.of_nat (length argvb))) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc a_main m)) c
/\ ART RT Σ m /\ mem_inv bsegs m /\ CLX OUT_rep ERR_rep XENV LIB stdout_init m /\ argv_rep argvb m ap
/\ stk bsegs m (rt_sp0 RT Σ - STACK_WIN) usp /\ sigma0_ok RT Σ usp
/\ usp mod 16 = 0 /\ usp < ap /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp
/\ X1cn.frm0 fc.

Definition OPENF (c : config) : Prop :=
exists (Σ : rts RT) (usp ap path : Z) (gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
ASTA RT Σ (PMfd fds0 fs)
(eq (entry_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
(Z_to_bv 64 path) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_open m)) c
/\ MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok RT Σ usp
/\ bytes_at bsegs m path (path_b argvb ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length (path_b argvb)) + 1 <= USTACK_TOP - 16
/\ path_slack argvb m path /\ X1cn.frm0 fc.

Definition OPENEDF (c : config) : Prop :=
exists (Σ : rts RT) (usp ap path : Z) (gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) ent
(F : bvmap 5 word) (fc : bv 32),
ASTA RT Σ (PMfd (fd_insert fds0 (Z_to_bv 64 3) ent) fs)
(ret_stF F fc (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 2) s1 (Z_to_bv 64 path)
s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 3) m) c
/\ MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok RT Σ usp
/\ bytes_at bsegs m path (path_b argvb ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length (path_b argvb)) + 1 <= USTACK_TOP - 16
/\ open_ent (path_b argvb) fs = Some ent /\ path_slack argvb m path /\ X1cn.frm0 fc.

End DrvF.

Lemma STARTF_START : forall RT OUT_rep ERR_rep XENV LIB argvb fs c,
STARTF RT OUT_rep ERR_rep XENV LIB argvb fs c -> START RT OUT_rep ERR_rep XENV LIB argvb fs c.
Proof.
intros RT OUT_rep ERR_rep XENV LIB argvb fs c
(Σ & usp & ap & gp & t0 & t1 & t2 & s0 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11
& t3 & t4 & t5 & t6 & F & fc & m & HA & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _FRM).
exists Σ, usp, ap, gp, t0, t1, t2, s0, s1, a2, a3, a4, a5, a6, a7, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6, F, fc, m.
exact (conj HA (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 H9))))))))).
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section DrvF.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.

Definition STARTF (c : config) : Prop :=
exists (Σ : rts RT) (usp ap : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
ASTA RT Σ (PMfd fds0 fs)
(eq (entry_st (Z_to_bv 64 MAIN_RA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
(Z_to_bv 64 (Z.of_nat (length argvb))) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc a_main m)) c
/\ ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB stdout_init m /\ argv_rep argvb m ap
/\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) usp /\ sigma0_ok RT Σ usp
/\ usp mod 16 = 0 /\ usp < ap /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp
/\ X1cn.frm0 fc.

Definition OPENF (c : config) : Prop :=
exists (Σ : rts RT) (usp ap path : Z) (gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
ASTA RT Σ (PMfd fds0 fs)
(eq (entry_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
(Z_to_bv 64 path) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_open m)) c
/\ MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok RT Σ usp
/\ bytes_at asegs m path (path_b argvb ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length (path_b argvb)) + 1 <= USTACK_TOP - 16
/\ path_slack argvb m path /\ X1cn.frm0 fc.

Definition OPENEDF (c : config) : Prop :=
exists (Σ : rts RT) (usp ap path : Z) (gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) ent
(F : bvmap 5 word) (fc : bv 32),
ASTA RT Σ (PMfd (fd_insert fds0 (Z_to_bv 64 3) ent) fs)
(ret_stF F fc (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 2) s1 (Z_to_bv 64 path)
s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 3) m) c
/\ MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok RT Σ usp
/\ bytes_at asegs m path (path_b argvb ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length (path_b argvb)) + 1 <= USTACK_TOP - 16
/\ open_ent (path_b argvb) fs = Some ent /\ path_slack argvb m path /\ X1cn.frm0 fc.

End DrvF.

Lemma STARTF_START : forall RT OUT_rep ERR_rep XENV LIB argvb fs c,
STARTF RT OUT_rep ERR_rep XENV LIB argvb fs c -> START RT OUT_rep ERR_rep XENV LIB argvb fs c.
Proof.
intros RT OUT_rep ERR_rep XENV LIB argvb fs c
(Σ & usp & ap & gp & t0 & t1 & t2 & s0 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11
& t3 & t4 & t5 & t6 & F & fc & m & HA & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _FRM).
exists Σ, usp, ap, gp, t0, t1, t2, s0, s1, a2, a3, a4, a5, a6, a7, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6, F, fc, m.
exact (conj HA (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 H9))))))))).
Qed.
