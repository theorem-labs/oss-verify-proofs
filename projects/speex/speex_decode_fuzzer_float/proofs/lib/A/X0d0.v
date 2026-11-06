(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0j3
X0il X0gp X0id X0i8 X0ib X0hx X0hv X0hm
X0fy X0fg X0e5 X0ci X0co.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X17w X19m X196 X17a X18y X18t X18w X18i X18g X187 X16j X161 X14q X133 X139.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X187 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X133 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X139.
Import ListNotations.
Open Scope Z_scope.

Section Cuts.
Variables (p : dlp) (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat) (s : secst).
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

Definition ds_loopmem (m : mem) : Prop :=
(exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G)
/\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
/\ drec_frame m C j (T + 208) (usp - 2128) (Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
/\ qcache_rep m C rest /\ qbatch m b (qfirst rest) ents.

Definition svc_mun : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (m' : mem),
ms = MSsvc (uod_regs (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s))
a2' a3' a4' a5' a6' (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6')
(dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) (dl_fc p) None m' (seg_rom bsegs)
/\ ARTc (recs Σk k) m' /\ mem_inv bsegs m'
/\ uod_frame m' (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x47f68) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1057944)
/\ stk bsegs m' (dl_lo p) (C - 112 - 48)
/\ ds_loopmem m'.

End Cuts.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section Cuts.
Variables (p : dlp) (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat) (s : secst).
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

Definition ds_loopmem (m : mem) : Prop :=
(exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G)
/\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
/\ drec_frame m C j (T + 208) (usp - 2128) (Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
/\ qcache_rep m C rest /\ qbatch m b (qfirst rest) ents.

Definition svc_mun : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (m' : mem),
ms = MSsvc (uod_regs (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s))
a2' a3' a4' a5' a6' (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6')
(dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) (dl_fc p) None m' (seg_rom asegs)
/\ ARTc (recs Σk k) m' /\ mem_inv asegs m'
/\ uod_frame m' (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x47e7c) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1023064)
/\ stk asegs m' (dl_lo p) (C - 112 - 48)
/\ ds_loopmem m'.

End Cuts.
