(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X0j1 X0gi X0j3 X0gd
X0g8 X0fy X0fg X0f1 X0fp.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X173 X19m X16y X16t X16j X161 X15m X16a.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16a.
Import ListNotations.
Open Scope Z_scope.

Definition rcore_entry (Σ : rtsA) (B : Z) (gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (n : Z)
(m : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x45e8c) (Z_to_bv 64 (B + -200)) gp (Z_to_bv 64 tpA) t0 t1 t2
(Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (l_T (lay Σ) + 208))
(Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
(Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
(Z_to_bv 64 7) (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) t3 t4 t5 t6)
F (Z_to_bv 64 0x4a424) fc None m (seg_rom bsegs).

Definition rcore_post (F : bvmap 5 word) (fc : bv 32) (Σ : rtsA) (PMc : Model -> Prop) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word)
(n lo : Z) (mX : mem) : config -> Prop :=
fun cf => exists (Σ' : rtsA) (p : Z),
ASTA RTA Σ' PMc (fun ms => exists m', ret_stF F fc (Z_to_bv 64 0x4676c) (Z_to_bv 64 (B + -72)) gp (Z_to_bv 64 tpA)
s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A (Z_to_bv 64 p) m' ms
/\ ART_A Σ' m' /\ mem_inv bsegs m' /\ wmono bsegs mX m' /\ stk bsegs m' lo (B + -72)
/\ rt_pres (live Σ) (frames Σ) (B + -72) mX m' /\ wr_at bsegs m' p n /\ acc bsegs m' p n) cf
/\ live Σ' = (p, n) :: live Σ /\ frames Σ' = frames Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ /\ credit Σ' = credit Σ - mcost n
/\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rtA_pois Σ' = rtA_pois Σ.

Definition core_stmt_realloc : Prop :=
forall (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z)
(gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (n lo : Z) (tr : list Z) (tb : list word) (j0 : list byte),
fdfs_only PMc -> mat_stable PMc -> 1 <= n <= 64512 ->
Z.of_nat (length (live Σ)) < LIVE_MAX -> mcost n <= credit Σ ->
ART_A Σ mX -> mem_inv bsegs mX ->
stk bsegs mX lo (B + -200) -> l_ACEIL (lay Σ) <= lo -> lo + 0x1000 <= B + -200 -> B + 2144 <= USTACK_TOP -> B mod 16 = 8 ->
In tr T_MAIN -> (1 <= length tr <= 5)%nat -> trc_cells B tr mX tb ->
raf_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0 ->
cps bsegs (ASTA RTA Σ PMc (eq (rcore_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
(rcore_post F fc Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition rcore_entry (Σ : rtsA) (B : Z) (gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (n : Z)
(m : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x45da0) (Z_to_bv 64 (B + -200)) gp (Z_to_bv 64 tpA) t0 t1 t2
(Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (l_T (lay Σ) + 208))
(Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
(Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
(Z_to_bv 64 7) (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) t3 t4 t5 t6)
F (Z_to_bv 64 0x4a338) fc None m (seg_rom asegs).

Definition rcore_post (F : bvmap 5 word) (fc : bv 32) (Σ : rtsA) (PMc : Model -> Prop) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word)
(n lo : Z) (mX : mem) : config -> Prop :=
fun cf => exists (Σ' : rtsA) (p : Z),
ASTA RTA Σ' PMc (fun ms => exists m', ret_stF F fc (Z_to_bv 64 0x46680) (Z_to_bv 64 (B + -72)) gp (Z_to_bv 64 tpA)
s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A (Z_to_bv 64 p) m' ms
/\ ART_A Σ' m' /\ mem_inv asegs m' /\ wmono asegs mX m' /\ stk asegs m' lo (B + -72)
/\ rt_pres (live Σ) (frames Σ) (B + -72) mX m' /\ wr_at asegs m' p n /\ acc asegs m' p n) cf
/\ live Σ' = (p, n) :: live Σ /\ frames Σ' = frames Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ /\ credit Σ' = credit Σ - mcost n
/\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rtA_pois Σ' = rtA_pois Σ.

Definition core_stmt_realloc : Prop :=
forall (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z)
(gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (n lo : Z) (tr : list Z) (tb : list word) (j0 : list byte),
fdfs_only PMc -> mat_stable PMc -> 1 <= n <= 64512 ->
Z.of_nat (length (live Σ)) < LIVE_MAX -> mcost n <= credit Σ ->
ART_A Σ mX -> mem_inv asegs mX ->
stk asegs mX lo (B + -200) -> l_ACEIL (lay Σ) <= lo -> lo + 0x1000 <= B + -200 -> B + 2144 <= USTACK_TOP -> B mod 16 = 8 ->
In tr T_MAIN -> (1 <= length tr <= 5)%nat -> trc_cells B tr mX tb ->
raf_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0 ->
cps asegs (ASTA RTA Σ PMc (eq (rcore_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
(rcore_post F fc Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).
