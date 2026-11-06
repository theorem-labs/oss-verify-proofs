(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Specs Fs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx X1cq X1d0 X1d7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0gp X0h2
X0j3 X0i7 X0fy X0fg X0e5 X0id X0i8 X0ib X0hx X0hv X0gj X0ci X0cp
X0cv X0e8 X0co X001 X0hi X0hs X0da X0e4 X0d9 X0cn X0ck X0cb X0hn X0g4
X0fq X0df X0g3 X0cr X0ca X0cs X0ce X0cd X0cl X0cq X0cm X00b
X0hh X0j0 X0il X0j4 X0hf X0hy X0d8 X0e6 X0c8 X0ic X0cw X0hm X0iz
X0hw X0gx X0iw X0iy X0ix X0db X0dc X0f1 X0d1 X0d3 X0d0 X0d2
X0cy X0d4 X0cz X0ew X0d6 X0d5 X0cc X0ct X0cu.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X17w X17a X17n X19m X18s X16j X161 X14q X18y X18t X18w X18i X18g X174 X133 X13a X13g X14t X139 X0r0 X183 X18d X13v X14p X13u X138 X135 X12w X188 X16p X16b X140 X16o X13c X12v X13d X12z X12y X136 X13b X137 X0ra X182 X19k X196 X19n X180 X18j X13t X14r X12t X18x X13h X187 X19j X18h X17i X19g X19i X19h X13w X13x X15m X13m X13o X13l X13n X13j X13p X13k X15h X13r X13q X12x X13e X13f.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X174 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X133 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X139 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X138 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X135 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X140 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X136 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X137 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X187 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13f.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Module RL_stmt.
Import X12c X0j9 X14x X0j1 X173 X18c X17w X17a X17n X19m X18s X16j X161 X14q.

Definition drain_stmt : Prop :=
forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
fdfs_only PMc -> mat_stable PMc ->
ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < qbytes (ql Σ) ->
qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6 ->
stk bsegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
mem_inv bsegs m ->
cps bsegs
(ASTA RTA Σ PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4a234) fc None m (seg_rom bsegs))))
(fun cf => exists Σ' : rtsA,
ASTA RTA Σ' PMc (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x46800) fc None m' (seg_rom bsegs)
/\ ART_A Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -2128)
/\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m') cf
/\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ rtA_pois Σ' = rtA_pois Σ).
End RL_stmt.
Export RL_stmt.

Module RL_drain_ldefs.
Import X12c X0j9 X14x X0j1 X173 X18c X17w X19m X17a X18y X18t X18w X18i X18g X174 X16j X161 X14q X133 X13a X13g.
Import RL_stmt.

Record dlp : Type := mkDLP {
dl_Σ0 : rtsA; dl_m0 : mem; dl_usp : Z; dl_lo : Z; dl_PMc : Model -> Prop;
dl_gp : word; dl_s10 : word; dl_s11 : word; dl_F : bvmap 5 word; dl_fc : bv 32;
dl_r0 : word; dl_r1 : word; dl_r2 : word; dl_r3 : word; dl_r4 : word; dl_r5 : word; dl_r6 : word; dl_r7 : word; dl_r8 : word;
dl_r9 : word }.

Definition wmono_out (G : list ivl) (m m' : mem) : Prop :=
forall x : word, wview bsegs m x <> None -> outside G (bv_unsigned x) -> wview bsegs m' x <> None.

Lemma wmono_out_nil : forall (m m' : mem), wmono bsegs m m' -> wmono_out [] m m'.
Proof. intros m m' H x Hx _. exact (H x Hx). Qed.
Lemma wmono_out_wmono : forall G (m1 m2 m3 : mem), wmono_out G m1 m2 -> wmono bsegs m2 m3 -> wmono_out G m1 m3.
Proof. intros G m1 m2 m3 H1 H2 x Hx Ho. exact (H2 x (H1 x Hx Ho)). Qed.
Lemma dl_outside_app : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof.
induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn [app outside] in *; [split; [exact I | exact H]|].
destruct H as (H1 & H2). destruct (IH W2 x H2) as (A & B). split; [split; [exact H1 | exact A] | exact B].
Qed.
Lemma wmono_out_trans : forall G1 G2 (m1 m2 m3 : mem), wmono_out G1 m1 m2 -> wmono_out G2 m2 m3 -> wmono_out (G2 ++ G1) m1 m3.
Proof.
intros G1 G2 m1 m2 m3 H1 H2 x Hx Ho. pose proof (dl_outside_app G2 G1 _ Ho) as (O2 & O1). exact (H2 x (H1 x Hx O1) O2).
Qed.

Section Vocab.
Variable p : dlp.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).

Definition dl_gone (G : list ivl) : Prop :=
Forall (fun r => forall a, fst r <= a < snd r -> ~ aclient (live Σ0) (frames Σ0) (C + 32) a /\ ~ (dl_lo p <= a < C + 32)) G.

Definition dl_mem (j : list byte) (Σk : rtsA) (rest : list batch) (m : mem) : Prop :=
ARTc Σk m /\ mem_inv bsegs m /\ stk bsegs m (dl_lo p) (C - 112) /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone G)
/\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
/\ drec_frame m C j (T + 208) (usp - 2056) (Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
/\ qcache_rep m C rest.

Definition dl_sig (Σk : rtsA) : Prop :=
lay Σk = lay Σ0 /\ live Σk = live Σ0 /\ frames Σk = frames Σ0 /\ credit Σk = credit Σ0 /\ ql Σk = [] /\ ca_init Σk = true /\ pois Σk = pois Σ0.

Definition dl_Q (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
(Z_to_bv 64 (C - 104)) (Z_to_bv 64 (fst (nth i ents (0%Z, 0%Z)))) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom bsegs)
/\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

Definition dl_N (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 0x47f68) (dl_fc p) None m (seg_rom bsegs)
/\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

Definition dl_D (j : list byte) (b : Z) (ents : list (Z * Z)) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR (Z_to_bv 64 0x47fa0) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
(Z_to_bv 64 (T + 208)) (Z_to_bv 64 INST) (Z_to_bv 64 24) (Z_to_bv 64 b) a4 a5 a6 a7
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) s6 s7 s8 s9
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 cdealloc_entry) (dl_fc p) None m (seg_rom bsegs)
/\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

Definition dl_B (j : list byte) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) s4 (Z_to_bv 64 (2^37)) s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 0x47fa0) (dl_fc p) None m (seg_rom bsegs)
/\ dl_mem j Σk rest m.

Definition dl_R (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR (Z_to_bv 64 0x47cac) (Z_to_bv 64 C) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a0 a1 a2 a3 a4 a5 a6 a7
(dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (ret_pc (Z_to_bv 64 0x47cac)) (dl_fc p) None m (seg_rom bsegs)
/\ ARTc Σk m /\ mem_inv bsegs m /\ stk bsegs m (dl_lo p) C /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone G)
/\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m /\ qcache_rep m C [].

Definition dl_fin : config -> Prop :=
fun cf => exists Σ' : rtsA, ASTA RTA Σ' (dl_PMc p) (dl_R Σ') cf /\ rt_wfP Σ' [] /\ dl_sig Σ'.

End Vocab.

Definition dl_av (Σ : rtsA) (zhi : Z) (W : list ivl) : Prop :=
(forall ib a n, nth_error (r_st (pr Σ 24)) ib = Some CkBatch -> p_abeg (l_SB (lay Σ)) 24 ib <= a ->
a + n <= p_abeg (l_SB (lay Σ)) 24 ib + 8192 -> disjoint_from W a n)
/\ (forall a n, zhi <= a -> a + n <= USTACK_TOP -> disjoint_from W a n).

Lemma qwf_of_wfP : forall Σ P, rt_wfP Σ P -> qwf (l_SB (lay Σ)) P.
Proof.
intros Σ P (H1 & HR & HV & HS & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & _).
unfold qallP in Q4, Q5, Q6. unfold qentsP, qallP in Q7.
split.
{ apply NoDup_ListNoDup in Q5. rewrite !map_app in Q5. apply NoDup_app_remove_l in Q5. apply NoDup_app_remove_l in Q5. exact Q5. }
apply Forall_forall. intros b Hb.
assert (Hb' : In b (ql Σ ++ qg Σ ++ P)) by (apply in_app_iff; right; apply in_app_iff; right; exact Hb).
destruct (proj1 (Forall_forall _ _) Q4 b Hb') as (i & Hi & Eb). pose proof (proj1 (Forall_forall _ _) Q6 b Hb') as Hl.
pose proof HR as (HR1 & _). pose proof (HR1 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W11).
pose proof H1 as (_ & _ & _ & _ & _ & HSB & _). change (ClassSize 24) with 8192 in W11.
assert (Hlt : (i < length (r_st (pr Σ 24)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
unfold p_abeg in Eb. change (ClassSize 24) with 8192 in Eb. unfold r24.
split; [rewrite Eb; apply Z.mod_divide; [lia|]; apply Z.mod_divide in HSB; [|lia]; destruct HSB as (q & Hq);
exists (q * 8 + 24 * 2 ^ 19 + Z.of_nat i); lia|].
split; [lia|]. split; [lia|]. split; [exact Hl|].
apply Forall_forall. intros e He.
assert (Hq : In e (flat_map snd (ql Σ ++ qg Σ ++ P))) by (apply in_flat_map; exists b; split; [exact Hb' | exact He]).
pose proof (qent_n_pos Σ e HR HS (proj1 (Forall_forall _ _) Q7 e Hq)). lia.
Qed.
End RL_drain_ldefs.
Export RL_drain_ldefs.

Module RL_drain_istmt.
Import X12c X0j9 X14x X0j1 X173 X18c X17w X19m X17a X18y X18i X18g X16j X161 X14q X14t X133.
Import RL_stmt RL_drain_ldefs.

Definition dl_ok (p : dlp) : Prop :=
fdfs_only (dl_PMc p) /\ mat_stable (dl_PMc p) /\ l_ACEIL (lay (dl_Σ0 p)) <= dl_lo p /\ dl_lo p + 0x4000 <= dl_usp p + -2208
/\ dl_usp p <= 2 ^ 47 /\ geo_ok (dl_Σ0 p).

Definition item_post (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) : config -> Prop :=
fun cf => exists Σk' : rtsA, ASTA RTA Σk' (dl_PMc p) (dl_N p j b ents i rest Σk') cf
/\ (rt_wfP Σk' ((b, skipn (S i) ents) :: rest) /\ dl_sig p Σk' /\ nth_error (r_st (pr Σk' 24)) ib = Some CkBatch).

Definition item_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps bsegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition item_prim_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (c : Z) (ic : nat) (n : Z),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
1 <= c <= 31 -> nth_error (r_st (pr Σk c)) ic = Some (CkQuar n) ->
nth i ents (0, 0) = (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16, n) ->
cps bsegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition item_sec_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (k : nat) (s : secst),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
nth_error (sec Σk) k = Some s -> s_quar s = true -> nth i ents (0, 0) = (s_mb s + 6128, s_n s) ->
cps bsegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition batch_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (rest : list batch),
rt_wfP Σk ((b, []) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps bsegs (ASTA RTA Σk (dl_PMc p) (dl_D p j b ents rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' (dl_PMc p) (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).
End RL_drain_istmt.
Export RL_drain_istmt.

Module RL_drain_loop.
Import X12c X0j9 X14x X0r0 X0j1 X173 X18c X17w X183 X18d X19m X17a X18y X18t X18w X18i X18g X16j X161 X13v X14p X14t X13u X14q X133 X13a X13g X138 X135 X12w.
Import RL_stmt RL_drain_ldefs RL_drain_istmt.

Lemma dl_cps_ex : forall (P : rtsA -> config -> Prop) (phi : rtsA -> Prop) (Q : config -> Prop),
(forall x, phi x -> cps bsegs (P x) Q) -> cps bsegs (fun cf => exists x, P x cf /\ phi x) Q.
Proof. intros P phi Q H T cf (x & HP & Hphi) Hk. exact (H x Hphi T cf HP Hk). Qed.

Lemma dl_evt : forall (Σk : rtsA) (PMc : Model -> Prop) (Pm Q : machine_state -> Prop), mat_stable PMc ->
(forall ms, Pm ms -> evt bsegs Q ms) -> cps bsegs (ASTA RTA Σk PMc Pm) (ASTA RTA Σk PMc Q).
Proof. intros Σk PMc Pm Q MST H. exact (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σk) _ _ _ (fl_ASTA_mat_stable Σk PMc MST) H). Qed.

Lemma geo_of_wfP : forall Σ P, rt_wfP Σ P -> geo_ok Σ.
Proof. intros Σ P (H1 & H2 & _ & H4 & _ & H6 & _). exact (conj H1 (conj H2 (conj H4 H6))). Qed.

Lemma hqb_of_wfP : forall Σ P, rt_wfP Σ P ->
Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Proof.
intros Σ P (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _). unfold qallP in Q4. rewrite app_assoc in Q4. apply Forall_app in Q4. exact (proj1 Q4).
Qed.

Section DLoop.
Variable p : dlp.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).
#[local] Notation FIN := (dl_fin p).
Hypothesis MST : mat_stable (dl_PMc p).
Hypothesis HLO : l_ACEIL (lay (dl_Σ0 p)) <= dl_lo p.
Hypothesis HLO2 : dl_lo p + 0x4000 <= dl_usp p + -2208.
Hypothesis HSP : dl_usp p <= 2 ^ 47.
Hypothesis HG0 : geo_ok (dl_Σ0 p).

Hypothesis ITEM : forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps bsegs (ASTA RTA Σk PMc (dl_Q p j b ents i rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_N p j b ents i rest Σk') cf
/\ (rt_wfP Σk' ((b, skipn (S i) ents) :: rest) /\ dl_sig p Σk' /\ nth_error (r_st (pr Σk' 24)) ib = Some CkBatch)).
Hypothesis BATCH : forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (rest : list batch),
rt_wfP Σk ((b, []) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps bsegs (ASTA RTA Σk PMc (dl_D p j b ents rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).

Lemma dl_nums : 0 < SB /\ SB_ok (l_ACEIL (lay Σ0)) SB /\ r24 SB + 2 ^ 32 <= lo /\ 0x65b000 <= lo /\ lo + 0x400 <= C - 112
/\ C + 32 <= 2 ^ 47 /\ 0 <= T + 208 < 2 ^ 64 /\ 0 <= usp - 2056 < 2 ^ 64 /\ l_ACEIL (lay Σ0) <= lo.
Proof using HLO HLO2 HSP HG0.
pose proof (dk_geo Σ0 HG0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (g_prb Σ0 HG0) as (P1 & P2 & P3).
pose proof (g_grant Σ0 HG0 T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (T1 & T2 & T3 & T4 & T5).
assert (HSB : SB_ok (l_ACEIL (lay Σ0)) SB).
{ pose proof (dg_ok Σ0 HG0) as (_ & X & _). exact X. }
pose proof HSB as (S1 & S2 & S3 & S4). unfold r24, kHighShadowEnd, SEGTOP_A in *.
repeat split; try assumption; lia.
Qed.

Lemma dl_bslot : forall Σk ib, geo_ok Σk -> lay Σk = lay Σ0 -> nth_error (r_st (pr Σk 24)) ib = Some CkBatch ->
0 < p_abeg SB 24 ib /\ p_abeg SB 24 ib + 8192 <= lo /\ r24 SB <= p_abeg SB 24 ib /\ p_abeg SB 24 ib + 8192 <= r24 SB + 2 ^ 32.
Proof using HLO HLO2 HSP HG0.
intros Σk ib HG El Hib. pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof (dk_slot_in Σk HG 24 ib _ ltac:(lia) Hib) as (S1 & S2 & S3 & S4 & S5 & S6). rewrite El in *.
change (ClassSize 24) with 8192 in *. unfold rb, r24, kUserCap in *. repeat split; lia.
Qed.

Lemma dl_mem_step : forall j Σk rest rest' (m m' : mem) (W : list ivl), dl_mem p j Σk rest m -> geo_ok Σk -> dl_sig p Σk ->
live_wf Σk -> depot_ok (dep Σk) (l_DNB (lay Σk)) (l_SSB (lay Σk)) (l_ACEIL (lay Σk)) ->
Forall (fun b => exists j, nth_error (r_st (pr Σk 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σk)) 24 j) (ql Σk ++ qg Σk) ->
Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) W -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
stk bsegs m' lo (C - 112) ->
drec_mem m' C SB j (T + 208) (usp - 2056) (Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest' ->
dl_mem p j Σk rest' m'.
Proof using HLO HLO2 HSP HG0.
intros j Σk rest rest' m m' W (A & MI & ST & WM0 & RP & FR & QR) HG (El & Elv & Efr & _) Hlive Hdep HQB HW MU WM MI' ST' (FR' & _ & QR').
pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
split; [exact (artc_stk Σk m m' W lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
split; [exact MI'|]. split; [exact ST'|]. split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
split; [|split; [exact FR' | exact QR']].
pose proof (client_stk Σk m m' W lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
intros a Ha. rewrite (RP' a Ha). exact (RP a Ha).
Qed.

Lemma dl_drec : forall j Σk rest (m : mem), dl_mem p j Σk rest m -> lay Σk = lay Σ0 ->
drec_mem m C SB j (T + 208) (usp - 2056) (Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest.
Proof.
intros j Σk rest m (A & _ & _ & _ & _ & FR & QR) El. split; [exact FR|]. split; [|exact QR].
pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
exact (proj1 IC1).
Qed.

Lemma dl_batch_of : forall Σk b ents rest, rt_wfP Σk ((b, ents) :: rest) ->
exists ib, nth_error (r_st (pr Σk 24)) ib = Some CkBatch /\ b = p_abeg (l_SB (lay Σk)) 24 ib.
Proof.
intros Σk b ents rest (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _). unfold qallP in Q4.
assert (Hb : In (b, ents) (ql Σk ++ qg Σk ++ (b, ents) :: rest)) by (apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
destruct (proj1 (Forall_forall _ _) Q4 _ Hb) as (ib & Hib & Eb). exists ib. split; [exact Hib | exact Eb].
Qed.

Lemma dl_from_N : forall k j Σk b ib ents i rest, length ents = (S i + k)%nat ->
rt_wfP Σk ((b, skipn (S i) ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps bsegs (ASTA RTA Σk PMc (dl_N p j b ents i rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
induction k as [|k IH]; intros j Σk b ib ents i rest Hlen HWP HS Hib Eb.
-
assert (Hsk : skipn (S i) ents = []) by (apply skipn_all2; lia).
rewrite Hsk in HWP.
eapply (cps_seq bsegs); [|exact (BATCH j Σk b ib ents rest HWP HS Hib Eb)].
apply (dl_evt Σk PMc _ _ MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HS as (El & _).
pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4). rewrite El in Eb. subst b.
pose proof DM as (_ & MI & ST & _).
eapply evt_mono; [apply (drec_next_deal_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (usp - 2056) j
(Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
(dl_r8 p) (dl_r9 p) _ ents rest i)|].
1: lia. 1: exact B3. 1: exact B4. 1: exact N2. 1: lia. 1: exact (dl_drec j Σk rest m DM El). 1: exact QB. 1: exact ST. 1: exact N3.
1: lia. 1: lia. 1: exact MI.
intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
exact (dl_mem_step j Σk rest rest m m' [] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP) (Forall_nil _) MU WM MI' ST' DM').
-
pose proof HS as (El & _).
eapply (cps_seq bsegs); [| eapply (cps_seq bsegs); [exact (ITEM j Σk b ib ents (S i) rest ltac:(lia) HWP HS Hib Eb)|]].
+ apply (dl_evt Σk PMc _ _ MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4). rewrite El in Eb. subst b.
pose proof DM as (_ & MI & ST & _).
eapply evt_mono; [apply (drec_next_qcb_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2056) j
(Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
(dl_r8 p) (dl_r9 p) _ ents rest i)|].
1: lia. 1: exact B1. 1: exact B2. 1: exact (dl_drec j Σk rest m DM El). 1: exact QB. 1: exact ST. 1: lia. 1: lia. 1: exact MI.
intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
exact (dl_mem_step j Σk rest rest m m' [] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP) (Forall_nil _) MU WM MI' ST' DM').
+ apply dl_cps_ex. intros Σk' (HWP' & HS' & Hib').
pose proof HS' as (El' & _).
exact (IH j Σk' b ib ents (S i) rest ltac:(lia) HWP' HS' Hib' ltac:(rewrite El', <- El; exact Eb)).
Qed.

Lemma dl_from_Q0 : forall j Σk b ib ents rest, ents <> [] -> rt_wfP Σk ((b, ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps bsegs (ASTA RTA Σk PMc (dl_Q p j b ents 0 rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
intros j Σk b ib ents rest Hne HWP HS Hib Eb. pose proof HS as (El & _).
destruct ents as [|e es]; [congruence|].
eapply (cps_seq bsegs); [exact (ITEM j Σk b ib (e :: es) 0 rest ltac:(cbn; lia) HWP HS Hib Eb)|].
apply dl_cps_ex. intros Σk' (HWP' & HS' & Hib'). pose proof HS' as (El' & _).
exact (dl_from_N (length es) j Σk' b ib (e :: es) 0 rest ltac:(cbn; lia) HWP' HS' Hib' ltac:(rewrite El', <- El; exact Eb)).
Qed.

Lemma dl_from_B : forall j rest Σk, rt_wfP Σk rest -> dl_sig p Σk -> cps bsegs (ASTA RTA Σk PMc (dl_B p j rest Σk)) FIN.
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
intros j. induction rest as [|[b ents] rest IH]; intros Σk HWP HS; pose proof HS as (El & _);
pose proof (geo_of_wfP _ _ HWP) as HG; pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _);
pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
-
eapply (cps_seq bsegs).
+ apply (dl_evt Σk PMc _ (dl_R p Σk) MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
pose proof DM as (A & MI & ST & WM0 & RP & _).
eapply evt_mono; [apply (drec_loop_ret_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2056) j
(Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
(dl_r8 p) (dl_r9 p))|].
1: exact (dl_drec j Σk [] m DM El). 1: exact ST. 1: lia. 1: exact N4. 1: exact N6. 1: exact MI.
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & QR' & ST').
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
split; [exact (artc_stk Σk m m' [] lo (C + 32) HG HL (Forall_nil _) A Hdep (hqb_of_wfP _ _ HWP) MU WM)|].
split; [exact MI'|]. split; [exact ST'|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|]. split; [|exact QR'].
pose proof (client_stk Σk m m' [] lo (C + 32) HG HL ltac:(lia) (Forall_nil _) Hlive MU) as RP'.
pose proof HS as (_ & Elv & Efr & _). rewrite Elv, Efr in RP'.
intros a Ha. rewrite (RP' a Ha). exact (RP a Ha).
+ intros T0 cf Hcf Hk. apply Hk. exists Σk. split; [exact Hcf | split; [exact HWP | exact HS]].
- destruct (dl_batch_of Σk b ents rest HWP) as (ib & Hib & Eb).
pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4).
assert (QW : qwf SB ((b, ents) :: rest)) by (pose proof (qwf_of_wfP _ _ HWP) as X; rewrite El in X; exact X).
assert (QB : X16j.qbytes ((b, ents) :: rest) <= 2 ^ 40) by (destruct HWP as (_ & _ & _ & _ & (_ & _ & X & _) & _); exact X).
rewrite qbytes_eq in QB.
destruct ents as [|e es].
+
eapply (cps_seq bsegs); [| eapply (cps_seq bsegs); [exact (BATCH j Σk b ib [] rest HWP HS Hib Eb)|]].
* apply (dl_evt Σk PMc _ _ MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
pose proof DM as (_ & MI & ST & _).
eapply evt_mono; [apply (drec_loop_deal_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (usp - 2056)
j (Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p)
(dl_r7 p) (dl_r8 p) (dl_r9 p) b rest)|].
1: exact QW. 1: lia. 1: exact N2. 1: lia. 1: exact (dl_drec j Σk _ m DM El). 1: exact ST. 1: exact N3. 1: lia. 1: lia. 1: exact MI.
intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
exact (dl_mem_step j Σk _ rest m m' [(C, C + 32)] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP)
ltac:(repeat constructor; cbn [fst snd]; lia) MU WM MI' ST' DM').
* apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (IH Σk' HWP' HS').
+
eapply (cps_seq bsegs); [| eapply (cps_seq bsegs); [exact (dl_from_Q0 j Σk b ib (e :: es) rest ltac:(discriminate) HWP HS Hib Eb)|]].
* apply (dl_evt Σk PMc _ _ MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
pose proof DM as (_ & MI & ST & _).
eapply evt_mono; [apply (drec_loop_qcb_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2056)
j (Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p)
(dl_r7 p) (dl_r8 p) (dl_r9 p) b (e :: es) rest)|].
1: discriminate. 1: exact QW. 1: lia. 1: exact N1. 1: exact (dl_drec j Σk _ m DM El). 1: exact ST. 1: exact N3. 1: lia. 1: lia. 1: exact MI.
intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
exact (dl_mem_step j Σk _ rest m m' [(C, C + 32)] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP)
ltac:(repeat constructor; cbn [fst snd]; lia) MU WM MI' ST' DM').
* apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (IH Σk' HWP' HS').
Qed.

End DLoop.
End RL_drain_loop.
Export RL_drain_loop.

Module RL_drain_itemp.
Import X12c X0j9 X14x X0r0 X0j1 X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18w X18i X18g X174 X16j X161 X13v X16p X16b X14p X14t X13u X14q X140 X16o X133 X13c X13a X138 X12v X135 X13d X12z X12y.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop.

Lemma skipn_nth_cons : forall {X} (l : list X) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof. intros X l. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma cps_pointwise : forall (Σ : rtsA) (PMc : Model -> Prop) (Pm : machine_state -> Prop) (Q : config -> Prop),
(forall ms, Pm ms -> cps bsegs (ASTA RTA Σ PMc (eq ms)) Q) -> cps bsegs (ASTA RTA Σ PMc Pm) Q.
Proof.
intros Σ PMc Pm Q H T cf (H1 & H2 & H3 & H4) Hk. apply (H _ H2 T cf); [|exact Hk].
split; [exact H1|]. split; [reflexivity|]. split; [exact H3 | exact H4].
Qed.

Lemma pres_munch : forall L F z (m m' : mem), rt_pres L F z m m' -> munch [(0, z); (USTACK_TOP, 2 ^ 64)] m m'.
Proof.
intros L F z m m' H x Hx. apply H. cbn [outside] in Hx. left.
pose proof (bv_unsigned_in_range 64 x) as X. unfold bv_modulus in X. cbn [Z.of_N] in X. lia.
Qed.

Lemma rt_pres_mono : forall L F z z' (m m' : mem), rt_pres L F z m m' -> z <= z' -> rt_pres L F z' m m'.
Proof. intros L F z z' m m' H Hz a Ha. apply H. destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha]. Qed.

Lemma rt_pres_trans : forall L F z (m1 m2 m3 : mem), rt_pres L F z m1 m2 -> rt_pres L F z m2 m3 -> rt_pres L F z m1 m3.
Proof. intros L F z m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Section IpGeo.
Variables (Σ : rtsA) (c : Z) (ic : nat) (n C lo : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hic : nth_error (r_st (pr Σ c)) ic = Some (CkQuar n).
Hypothesis HL1 : l_ACEIL (lay Σ) <= lo.
Hypothesis HL2 : lo <= C - 1136.
Hypothesis HL3 : C <= 2 ^ 47.
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c ic).
#[local] Notation W12 := (W_QCB (p_abeg (l_SB (lay Σ)) c ic) (p_abeg (l_SB (lay Σ)) c ic + rz_size n - 16) n (l_T (lay Σ)) C
++ W_CD (l_T (lay Σ)) (l_SB (lay Σ)) c (C - 112)).

Lemma ip_facts : AB + 8 <= AB + ClassSize c /\ AB <= AB + rz_size n - 16 /\ AB + rz_size n - 16 + 4 <= AB + ClassSize c
/\ SHB <= shad (AB + rz_size n - 16 + 16) /\ shad (AB + rz_size n - 16 + 16) + ru8 n / 8 <= 2 ^ 44 + SHB
/\ SHB <= shad (rb SB c + kUserCap) /\ shad (rb SB c + 2 ^ 32) <= 2 ^ 44 + SHB
/\ AB + ClassSize c <= SB + 2 ^ 37 /\ 0 <= AB.
Proof using HG Hc Hic.
clear HL1 HL2 HL3. pose proof (qp_fit Σ c ic n HG Hc Hic) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
pose proof (qp_slot Σ c ic n HG Hc Hic) as (P1 & P2 & P3 & P4 & P5 & G1 & G2 & G3).
pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4). pose proof (dk_geo Σ HG) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
pose proof (shad_len (AB + rz_size n - 16 + 16) (ru8 n) ltac:(lia) ltac:(lia) ltac:(lia)) as (SL1 & SL2).
assert (Z.max 0 (ru8 n / 8) = ru8 n / 8) by (apply Z.max_r; apply Z.div_pos; lia).
pose proof (shad_len (rb SB c + kUserCap) (2 ^ 32 - kUserCap) ltac:(unfold rb, kUserCap in *; lia) ltac:(unfold kUserCap; lia)
ltac:(unfold rb, kUserCap in *; lia)) as (SL3 & _).
pose proof (fk_shad_mono (rb SB c + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
repeat split; lia.
Qed.

Lemma ip_batch_av : forall j', nth_error (r_st (pr Σ 24)) j' = Some CkBatch -> disjoint_from W12 (p_abeg SB 24 j') 8192.
Proof using HG Hc Hic HL1 HL2 HL3.
intros j' Hj.
pose proof ip_facts as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
pose proof (g_slot_apart Σ HG c ic 24 j' _ _ Hc ltac:(lia) Hic Hj
ltac:(destruct (Z.eq_dec c 24) as [->|X]; [right; intros <-; rewrite Hic in Hj; discriminate | left; exact X])) as AP.
change (ClassSize 24) with 8192 in AP.
pose proof (dk_slot_in Σ HG 24 j' _ ltac:(lia) Hj) as (U1 & U2 & U3 & U4 & U5 & U6). change (ClassSize 24) with 8192 in *.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5). pose proof HSB as (Y1 & Y2 & Y3 & Y4).
assert (HTT : T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
unfold W_QCB, W_CD. cbn [app disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB, kHighShadowEnd in *.
repeat split; lia.
Qed.

Lemma ip_stack_av : forall a k, C - 112 <= a -> 0 <= k -> disjoint_from W12 a k.
Proof using HG Hc Hic HL1 HL2 HL3.
intros a k Ha Hk.
pose proof ip_facts as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5).
unfold W_QCB, W_CD. cbn [app disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
repeat split; lia.
Qed.

End IpGeo.

Lemma dl_batch_of_in : forall Σk P b' ents', rt_wfP Σk P -> In (b', ents') P ->
exists j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch /\ b' = p_abeg (l_SB (lay Σk)) 24 j'.
Proof.
intros Σk P b' ents' (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _) Hin. unfold qallP in Q4.
assert (Hb : In (b', ents') (ql Σk ++ qg Σk ++ P)) by (apply in_app_iff; right; apply in_app_iff; right; exact Hin).
destruct (proj1 (Forall_forall _ _) Q4 _ Hb) as (j' & Hj & Eb). exists j'. split; [exact Hj | exact Eb].
Qed.

Section ItemP.
Variable p : dlp.
Hypothesis FC : fixed_commit_node.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).

Theorem item_prim_ok : item_prim_stmt p.
Proof using FC HOK.
intros j Σk b ib ents i rest c ic n Hi HWP HS Hib Eb Hc Hic Hent.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & HR & Hlive & HSW & HQW & HFW & HB & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
pose proof (proj1 (proj2 (proj2 HR)) c Hc) as (Hcnt & _ & Hcl0).
assert (Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σk c)))) (ca Σk c)) by (eapply Forall_impl; [|exact Hcl0]; intros x (X & _); exact X).
pose proof (proj1 HR c Hc) as HRW.
assert (HAw : A_bytes (aw Σk) <= CREDIT0) by (destruct HB as (X1 & _ & X3 & _); lia).
assert (HEg : rt_eager (recp Σk c ic) <= 2 ^ 38)
by (exact (proj1 (proj2 (proj2 (proj2 (budget_wf_recp Σk c ic (CkQuar n) HB HR HSW Hc Hic ltac:(discriminate) Einit)))))).

assert (Esk : skipn i ents = (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16, n) :: skipn (S i) ents)
by (rewrite (skipn_nth_cons ents i (0, 0) Hi), Hent; reflexivity).
rewrite Esk in HWP.
pose proof (rt_wfP_recp Σk b _ n (skipn (S i) ents) rest c ic HWP Hc Hic eq_refl Einit) as HWP'.
apply cps_pointwise. intros ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof FR as (FR1 & FR2 & FR3). pose proof FR2 as CBP0.
apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 (l_T (lay Σ0) + 208))] [C8 (Z_to_bv 64 (usp - 2056))])) in CBP0.
destruct CBP0 as (CBP & _). rewrite <- El in CBP.
rewrite Hent. cbn [fst].
eapply (cps_seq bsegs).
{ eapply (dl_evt Σk PMc _ _ MST). intros ms0 <-.
exact (qcbp_evt Σk m C lo c ic n (dl_gp p) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1057944)
(Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) HG HA Hc Hic CBP ST HLk ltac:(lia) ltac:(lia) MI Hlive Hdep HQB). }
apply cps_pointwise. intros ms1 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & HA1 & MU1 & WM1 & MI1 & ST1 & RP1).
assert (Esp : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
eapply (cps_conseq bsegs).
- exact (cd_lift Σk PMc m1 c ic (CkQuar n) lo (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' (Z_to_bv 64 C)
(Z_to_bv 64 INST) a4' a5' a6' a7' (Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37))
(Z_to_bv 64 (Z.of_nat (length ents))) (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16))
(Z_to_bv 64 (16 + Z.of_nat i)) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p)
FDO MST FC HG HA1 Hc Hic Einit HRW Hcl Hcnt ltac:(rewrite Esp; exact ST1) HLk ltac:(rewrite Esp; lia) ltac:(rewrite Esp; lia)
MI1 Hlive Hdep HQB HL HAw HEg).
- intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms E; rewrite <- E; reflexivity | intros mo X; exact X].
- intros cf Hcf. exists (recp Σk c ic). split.
+ unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & HA2 & MU2 & WM2 & MI2 & ST2 & RP2).
rewrite Esp in MU2, ST2, RP2.
rewrite (ret_pc_even 0x47f68); [| lia | reflexivity].
exists (Z_to_bv 64 0x47f68), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
assert (RPa : rt_pres (live Σ0) (frames Σ0) (C - 112) m m2).
{ rewrite <- Elv, <- Efr. exact (rt_pres_trans _ _ _ m m1 m2 RP1 RP2). }
pose proof (pres_munch _ _ _ m m2 RPa) as MUa.
assert (WMa : wmono bsegs m m2) by exact (wmono_trans _ _ _ _ WM1 WM2).
assert (MUb : munch (W_QCB (p_abeg (l_SB (lay Σk)) c ic) (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16) n (l_T (lay Σk)) C
++ W_CD (l_T (lay Σk)) (l_SB (lay Σk)) c (C - 112)) m m2).
{ apply (munch_trans _ m m1 m2); eapply munch_weaken; [| exact MU1 | | exact MU2]; intros x Hx; apply outside_app_inv in Hx; destruct Hx as [Hx1 Hx2]; first [exact Hx1 | exact Hx2]. }
assert (HBAV : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from (W_QCB (p_abeg (l_SB (lay Σk)) c ic)
(p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16) n (l_T (lay Σk)) C ++ W_CD (l_T (lay Σk)) (l_SB (lay Σk)) c (C - 112))
(p_abeg (l_SB (lay Σk)) 24 j') 8192)
by exact (ip_batch_av Σk c ic n C lo HG Hc Hic HLk ltac:(lia) ltac:(lia)).
split.
* split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m2 WG WMa) | exact HGo]|].
split; [exact (rt_pres_trans _ _ _ _ m m2 RP (rt_pres_mono _ _ (C - 112) (C + 32) m m2 RPa ltac:(lia)))|].
split.
-- split; [|split].
++ apply (rw_cells_transport bsegs _ m m2 _ _ FR1 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
++ apply (rw_cells_transport bsegs _ m m2 _ _ FR2 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
++ apply (rw_cells_transport bsegs _ m m2 _ _ FR3 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (qcache_rep_frame _ m m2 C rest QR MUb WMa).
++ exact (ip_stack_av Σk c ic n C lo HG Hc Hic HLk ltac:(lia) ltac:(lia) C 32 ltac:(lia) ltac:(lia)).
++ apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (HBAV j' Hj').
* apply (qbatch_frame _ m m2 b (qfirst rest) ents QB MUb WMa). rewrite Eb. exact (HBAV ib Hib).
+ split; [exact HWP'|]. split.
* pose proof (recp_fields Σk c ic) as (X1 & X2 & _ & _ & _ & X6 & _ & _ & _ & _ & _ & X12 & X13 & X14).
split; [rewrite X1; exact El|]. split; [rewrite X13; exact Elv|]. split; [rewrite X14; exact Efr|].
split; [rewrite X12; exact Ecr|]. split; [rewrite X6; exact Eql | split; [rewrite X2; exact Einit | exact Epo]].
* rewrite recp_st. destruct (Z.eqb_spec 24 c) as [E24|N24]; cbn [andb]; [|exact Hib].
destruct (Nat.eqb_spec ic ib) as [<-|X]; [| exact Hib]. rewrite <- E24 in Hic. rewrite Hic in Hib. discriminate.
Qed.

End ItemP.
End RL_drain_itemp.
Export RL_drain_itemp.

Module RL_drain_batch.
Import X12c X0j9 X14x X0r0 X0j1 X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18w X18i X18g X174 X16j X161 X13v X16p X16b X14p X14t X13u X14q X140 X16o X133 X13c X13a X138 X12v X135 X12z X12y.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp.

Lemma stk_of_bytes_wr : forall (m : mem) a bs, bytes_at bsegs m a bs -> wr_at bsegs m a (Z.of_nat (length bs)) ->
stk bsegs m a (a + Z.of_nat (length bs)).
Proof.
intros m a bs (B0 & B1 & Hb) (W0 & W1 & Hw). split; [exact B0|]. split; [lia|]. intros x Hx.
split; [replace x with (a + (x - a)) by lia; apply Hw; lia|].
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite Hb by lia.
destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma qbatch_stk : forall (m : mem) b nxt ents, qbatch m b nxt ents -> stk bsegs m b (b + 8192).
Proof.
intros m b nxt ents (H & (ws & U & Hl & _) & _).
destruct H as ((_ & Hb) & Hw). cbn [cells_bytes cbytes] in Hb. rewrite !app_nil_r in Hb.
pose proof (stk_of_bytes_wr m b _ Hb ltac:(rewrite !length_app, !length_le8; exact Hw)) as S1.
rewrite !length_app, !length_le8 in S1. change (Z.of_nat (8 + (8 + 8))) with 24 in S1.
destruct U as (Ub & Uw). pose proof (stk_of_bytes_wr m (b + 0x18) _ Ub ltac:(rewrite u64s_length, Nat2Z.inj_mul; exact Uw)) as S2.
rewrite u64s_length, Hl in S2. change (Z.of_nat (8 * 1021)) with 8168 in S2.
destruct S1 as (A0 & A1 & Aw). destruct S2 as (C0 & C1 & Cw). split; [lia|]. split; [lia|]. intros x Hx.
destruct (Z_lt_ge_dec x (b + 24)) as [X|X]; [apply Aw; lia | apply Cw; lia].
Qed.

Lemma artc_unbatch : forall (Σ : rtsA) (m : mem) ib, ARTc Σ m -> nth_error (r_st (pr Σ 24)) ib = Some CkBatch ->
stk bsegs m (p_abeg (l_SB (lay Σ)) 24 ib) (p_abeg (l_SB (lay Σ)) 24 ib + 8192) -> ARTc (set_st Σ 24 ib CkIdle) m.
Proof.
intros Σ m ib HA Hib ST. destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
apply ARTc_intro.
- exact A1.
- intros c' Hc'. destruct (Z.eq_dec c' 24) as [->|Hne].
+ rewrite set_st_pr_same'. apply reg_rep_ureg'. exact (A2 24 Hc').
+ rewrite (set_st_pr_other' Σ 24 ib CkIdle c' Hne). exact (A2 c' Hc').
- exact A3.
- destruct A4 as [P Sc]. split; [|exact Sc].
intros c' i' st Hc' Hn'. destruct (Z.eq_dec c' 24) as [->|Hne].
+ rewrite set_st_pr_same' in Hn'. unfold ureg in Hn'. cbn [r_st] in Hn'. rewrite nth_upd_ck in Hn'.
destruct (Nat.eqb_spec ib i') as [<-|Hii].
* destruct (Nat.ltb_spec ib (length (r_st (pr Σ 24)))); [|discriminate]. injection Hn' as <-.
pose proof (P 24 ib CkBatch Hc' Hib) as X. cbn [pchunk] in X |- *. split; [exact ST | exact X].
* exact (P 24 i' st Hc' Hn').
+ rewrite (set_st_pr_other' Σ 24 ib CkIdle c' Hne) in Hn'. exact (P c' i' st Hc' Hn').
- exact A5.
- exact A6.
- exact A7.
- exact A8.
- exact A9.
- exact A10.
- exact A11.
Qed.

Lemma bt_batch_av : forall (Σ : rtsA) j' C lo, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j' = Some CkBatch ->
l_ACEIL (lay Σ) <= lo -> lo <= C - 1136 -> C <= 2 ^ 47 ->
disjoint_from (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) 24 (C - 112)) (p_abeg (l_SB (lay Σ)) 24 j') 8192.
Proof.
intros Σ j' C lo HG Hj HL1 HL2 HL3.
pose proof (dk_slot_in Σ HG 24 j' _ ltac:(lia) Hj) as (U1 & U2 & U3 & U4 & U5 & U6). change (ClassSize 24) with 8192 in *.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG 24 ltac:(lia)) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5). pose proof HSB as (Y1 & Y2 & Y3 & Y4).
assert (HTT : l_T (lay Σ) + 4096 <= l_SB (lay Σ) \/ l_SB (lay Σ) + 2 ^ 37 + 4096 <= l_T (lay Σ)) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
pose proof (fk_shad_mono (rb (l_SB (lay Σ)) 24 + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB, kHighShadowEnd in *.
repeat split; lia.
Qed.

Lemma bt_stack_av : forall (Σ : rtsA) C lo a k, geo_ok Σ -> l_ACEIL (lay Σ) <= lo -> lo <= C - 1136 -> C <= 2 ^ 47 ->
C - 112 <= a -> 0 <= k -> disjoint_from (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) 24 (C - 112)) a k.
Proof.
intros Σ C lo a k HG HL1 HL2 HL3 Ha Hk.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG 24 ltac:(lia)) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5).
pose proof (fk_shad_mono (rb (l_SB (lay Σ)) 24 + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
repeat split; lia.
Qed.

Section Batch.
Variable p : dlp.
Hypothesis FC : fixed_commit_node.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).

Theorem batch_ok : batch_stmt p.
Proof using FC HOK.
intros j Σk b ib ents rest HWP HS Hib Eb.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & HR & Hlive & HSW & HQW & HFW & HB & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
pose proof (proj1 (proj2 (proj2 HR)) 24 ltac:(lia)) as (Hcnt & _ & Hcl0).
assert (Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σk 24)))) (ca Σk 24)) by (eapply Forall_impl; [|exact Hcl0]; intros x (X & _); exact X).
pose proof (proj1 HR 24 ltac:(lia)) as HRW.
assert (HAw : A_bytes (aw Σk) <= CREDIT0) by (destruct HB as (X1 & _ & X3 & _); lia).
assert (HEg : rt_eager (recp Σk 24 ib) <= 2 ^ 38)
by (exact (proj1 (proj2 (proj2 (proj2 (budget_wf_recp Σk 24 ib CkBatch HB HR HSW ltac:(lia) Hib ltac:(discriminate) Einit)))))).
pose proof (rt_wfP_batch Σk b rest ib HWP Hib Eb Einit) as HWP'.
apply cps_pointwise.
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof FR as (FR1 & FR2 & FR3).
assert (HA' : ARTc (set_st Σk 24 ib CkIdle) m).
{ apply (artc_unbatch Σk m ib HA Hib). rewrite <- Eb. exact (qbatch_stk m b _ ents QB). }
assert (Esp : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
eapply (cps_conseq bsegs).
- exact (cd_lift Σk PMc m 24 ib CkBatch lo (Z_to_bv 64 0x47fa0) (Z_to_bv 64 (C - 112)) (dl_gp p) t0 t1 t2 (Z_to_bv 64 C)
(Z_to_bv 64 INST) a4 a5 a6 a7 (Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37))
s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p)
FDO MST FC HG HA' ltac:(lia) Hib Einit HRW Hcl Hcnt ltac:(rewrite Esp; exact ST) HLk ltac:(rewrite Esp; lia) ltac:(rewrite Esp; lia)
MI Hlive Hdep HQB HL HAw HEg).
- intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms E. rewrite <- E. unfold cd_msD. rewrite <- Eb, El. reflexivity.
- intros cf Hcf. exists (recp Σk 24 ib). split.
+ unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & HA2 & MU2 & WM2 & MI2 & ST2 & RP2).
rewrite Esp in MU2, ST2, RP2.
rewrite (ret_pc_even 0x47fa0); [| lia | reflexivity].
exists (Z_to_bv 64 0x47fa0), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', (Z_to_bv 64 b), s6, s7, s8, s9,
t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
assert (RPa : rt_pres (live Σ0) (frames Σ0) (C - 112) m m2) by (rewrite <- Elv, <- Efr; exact RP2).
pose proof (pres_munch _ _ _ m m2 RPa) as MUa.
split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m2 WG WM2) | exact HGo]|].
split; [exact (rt_pres_trans _ _ _ _ m m2 RP (rt_pres_mono _ _ (C - 112) (C + 32) m m2 RPa ltac:(lia)))|].
split.
* split; [|split].
-- apply (rw_cells_transport bsegs _ m m2 _ _ FR1 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (rw_cells_transport bsegs _ m m2 _ _ FR2 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (rw_cells_transport bsegs _ m m2 _ _ FR3 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
* apply (qcache_rep_frame _ m m2 C rest QR MU2 WM2).
-- exact (bt_stack_av Σk C lo C 32 HG HLk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
-- apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'.
exact (bt_batch_av Σk j' C lo HG Hj' HLk ltac:(lia) ltac:(lia)).
+ split; [exact HWP'|].
pose proof (recp_fields Σk 24 ib) as (X1 & X2 & _ & _ & _ & X6 & _ & _ & _ & _ & _ & X12 & X13 & X14).
split; [rewrite X1; exact El|]. split; [rewrite X13; exact Elv|]. split; [rewrite X14; exact Efr|].
split; [rewrite X12; exact Ecr|]. split; [rewrite X6; exact Eql | split; [rewrite X2; exact Einit | exact Epo]].
Qed.

End Batch.
End RL_drain_batch.
Export RL_drain_batch.

Module RL_drain_rec.
Import X12c X0j9 X14x X0r0 X0j1 X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18s X18w X18i X18g X174 X16j X161 X13v X16p X16b X14p X14t X13u X14q X140 X16o X133 X13c X13a X13g X138 X135 X12w.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch.

Section DRec.
Variable p : dlp.
Hypothesis HOK : dl_ok p.
Hypothesis ITEM : item_stmt p.
Hypothesis BATCH : batch_stmt p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).

Definition dl_E (tmp : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR (Z_to_bv 64 0x47cac) (Z_to_bv 64 C) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) (Z_to_bv 64 QUAR)
(Z_to_bv 64 C) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp - 2056)) a4 a5 a6 a7 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p)
(dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 qdorec_entry) (dl_fc p) None m (seg_rom bsegs)
/\ ARTc Σk m /\ qcache_rep m C tmp /\ stk bsegs m lo C /\ mem_inv bsegs m
/\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G) /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m.

Lemma dl_mem_entry : forall j Σk rest (m m' : mem) (W : list ivl), ARTc Σk m -> (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G) ->
rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m -> geo_ok Σk -> dl_sig p Σk ->
live_wf Σk -> depot_ok (dep Σk) (l_DNB (lay Σk)) (l_SSB (lay Σk)) (l_ACEIL (lay Σk)) ->
Forall (fun b => exists j, nth_error (r_st (pr Σk 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σk)) 24 j) (ql Σk ++ qg Σk) ->
Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) W -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
stk bsegs m' lo (C - 112) ->
drec_mem m' C SB j (T + 208) (usp - 2056) (Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest ->
dl_mem p j Σk rest m'.
Proof using HOK.
intros j Σk rest m m' W A WM0 RP HG (El & Elv & Efr & _) Hlive Hdep HQB HW MU WM MI' ST' (FR' & _ & QR').
pose proof HOK as (_ & _ & HLO & HLO2 & HSP & HG0).
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
split; [exact (artc_stk Σk m m' W lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
split; [exact MI'|]. split; [exact ST'|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
split; [|split; [exact FR' | exact QR']].
pose proof (client_stk Σk m m' W lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
exact (rt_pres_trans _ _ _ _ m m' RP RP').
Qed.

Theorem dl_from_E : forall Σk tmp, rt_wfP Σk tmp -> dl_sig p Σk -> cps bsegs (ASTA RTA Σk PMc (dl_E tmp Σk)) (dl_fin p).
Proof using HOK ITEM BATCH.
intros Σk tmp HWP HS.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof HS as (El & Elv & Efr & _).
pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
destruct tmp as [|[b ents] rest].
-
eapply (cps_seq bsegs).
+ apply (dl_evt Σk PMc _ (dl_R p Σk) MST).
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
eapply evt_mono; [apply (drec_empty_spec (Z_to_bv 64 0x47cac) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
(dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m C lo (T + 208) (usp - 2056))|].
1: exact QR. 1: exact ST. 1: lia. 1: exact N4. 1: exact N6. 1: exact N7. 1: exact N8. 1: exact MI.
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & QR' & ST').
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
assert (HW : Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) [(C - 112, C)]) by (repeat constructor; cbn [fst snd]; lia).
split; [exact (artc_stk Σk m m' _ lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
split; [exact MI'|]. split; [exact ST'|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
split; [|exact QR'].
pose proof (client_stk Σk m m' _ lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
exact (rt_pres_trans _ _ _ _ m m' RP RP').
+ intros T0 cf Hcf Hk. apply Hk. exists Σk. split; [exact Hcf | split; [exact HWP | exact HS]].
- destruct (dl_batch_of Σk b ents rest HWP) as (ib & Hib & Eb).
pose proof (dl_bslot p HLO HLO2 HSP HG0 Σk ib HG El Hib) as (B1 & B2 & B3 & B4).
assert (QW : qwf SB ((b, ents) :: rest)) by (pose proof (qwf_of_wfP _ _ HWP) as X; rewrite El in X; exact X).
assert (QB : X16j.qbytes ((b, ents) :: rest) <= 2 ^ 40) by (destruct HWP as (_ & _ & _ & _ & (_ & _ & X & _) & _); exact X).
rewrite qbytes_eq in QB.
assert (HW : Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) [(C - 112, C + 32)]) by (repeat constructor; cbn [fst snd]; lia).
destruct ents as [|e es].
+
eapply (cps_seq bsegs).
* apply (dl_evt Σk PMc _ (fun ms => exists j, dl_D p j b [] rest Σk ms) MST).
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
destruct IC1 as (SBC & _).
eapply evt_mono; [apply (drec_first_deal_spec (Z_to_bv 64 0x47cac) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
(dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (usp - 2056) b rest)|].
1: exact QW. 1: lia. 1: exact N2. 1: exact QR. 1: exact SBC. 1: exact ST. 1: lia. 1: exact N3. 1: exact N4. 1: exact N6.
1: exact N7. 1: exact N8. 1: exact MI.
intros ms' (j & t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists j, t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
exact (dl_mem_entry j Σk rest m m' _ A WM0 RP HG HS Hlive Hdep HQB HW MU WM MI' ST' DM').
* apply cps_pointwise. intros ms (j & X).
eapply (cps_seq bsegs).
-- eapply (cps_conseq bsegs); [exact (BATCH j Σk b ib [] rest HWP HS Hib Eb) | | intros cf Hcf; exact Hcf].
intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms' <-; exact X | intros mo Y; exact Y].
-- apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (dl_from_B p MST HLO HLO2 HSP HG0 ITEM BATCH j rest Σk' HWP' HS').
+
eapply (cps_seq bsegs).
* apply (dl_evt Σk PMc _ (fun ms => exists j, dl_Q p j b (e :: es) 0 rest Σk ms) MST).
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
destruct IC1 as (SBC & _).
eapply evt_mono; [apply (drec_first_qcb_spec (Z_to_bv 64 0x47cac) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
(dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2056) b (e :: es) rest)|].
1: discriminate. 1: exact QW. 1: lia. 1: exact N1. 1: exact QR. 1: exact SBC. 1: exact ST. 1: lia. 1: exact N3. 1: exact N4. 1: exact N6.
1: exact N7. 1: exact N8. 1: exact MI.
intros ms' (j & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists j, t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
exact (dl_mem_entry j Σk rest m m' _ A WM0 RP HG HS Hlive Hdep HQB HW MU WM MI' ST' DM').
* apply cps_pointwise. intros ms (j & X).
eapply (cps_seq bsegs).
-- eapply (cps_conseq bsegs); [exact (dl_from_Q0 p MST HLO HLO2 HSP HG0 ITEM BATCH j Σk b ib (e :: es) rest ltac:(discriminate) HWP HS Hib Eb)
| | intros cf Hcf; exact Hcf].
intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms' <-; exact X | intros mo Y; exact Y].
-- apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (dl_from_B p MST HLO HLO2 HSP HG0 ITEM BATCH j rest Σk' HWP' HS').
Qed.

End DRec.
End RL_drain_rec.
Export RL_drain_rec.

Module RL_drain_xfer.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18d X18y X18s X18j X18w X16j X161 X13v X16p X13t X16b X14p X14t X13u X14q X14r X140 X133 X13c X13a X13g X138 X12t.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec.

Definition W_D (T usp : Z) (bw : list ivl) : list ivl :=
[(i_q_cmutex, i_q_cmutex + 4); (i_q_global, i_q_global + 32); (T + 80, T + 112)] ++ bw ++ [(usp - 2256, usp - 2208)].
Definition W_X (T usp : Z) (bw : list ivl) : list ivl := W_D T usp bw ++ [(usp - 2208, usp - 2128)].
Definition TZ_X (T : Z) : list ivl := [(T + 80, T + 112)].

Lemma xq_cells : forall Σ m, ARTc Σ m ->
qcache_rep m (l_T (lay Σ) + 80) (ql Σ) /\ qcache_rep m QG (qg Σ) /\ q_lock m 0 0
/\ rw_cells bsegs m q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)].
Proof.
intros Σ m (A1 & _ & _ & _ & _ & (Q1 & Q2 & Q3) & _). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
destruct A1 as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
repeat match type of IC with _ /\ ?R => destruct IC as [?X IC] end.
match goal with H : rw_cells bsegs m i_q_max _ |- _ => exact H end.
Qed.

Lemma qwf_of_wfx : forall Σ, rt_wfx Σ -> qwf (l_SB (lay Σ)) (qg Σ ++ ql Σ).
Proof.
intros Σ (H1 & HR & HV & HS & (Q1 & Q2 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & _).
assert (GQ : Permutation (ql Σ ++ qg Σ) (qg Σ ++ ql Σ)) by apply Permutation_app_comm.
split; [apply (Permutation_NoDup (Permutation_map fst GQ)); apply NoDup_ListNoDup; exact Q5|].
apply (Permutation_Forall GQ). apply Forall_forall. intros b Hb.
destruct (proj1 (Forall_forall _ _) Q4 b Hb) as (i & Hi & Eb). pose proof (proj1 (Forall_forall _ _) Q6 b Hb) as Hl.
pose proof HR as (HR1 & _). pose proof (HR1 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W11).
pose proof H1 as (_ & _ & _ & _ & _ & HSB & _). change (ClassSize 24) with 8192 in W11.
assert (Hlt : (i < length (r_st (pr Σ 24)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
unfold p_abeg in Eb. change (ClassSize 24) with 8192 in Eb. unfold r24.
split; [rewrite Eb; apply Z.mod_divide; [lia|]; apply Z.mod_divide in HSB; [|lia]; destruct HSB as (q & Hq);
exists (q * 8 + 24 * 2 ^ 19 + Z.of_nat i); lia|].
split; [lia|]. split; [lia|]. split; [exact Hl|].
apply Forall_forall. intros e He.
assert (Hq : In e (qents Σ)) by (unfold qents; apply in_flat_map; exists b; split; [exact Hb | exact He]).
pose proof (qent_n_pos Σ e HR HS (proj1 (Forall_forall _ _) Q7 e Hq)). lia.
Qed.

Definition dpost (F : bvmap 5 word) (fc : bv 32) (Σ' : rtsA) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (live0 : list (Z * Z))
(frames0 : list (Z * nat)) (m : mem) : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x46800) fc None m' (seg_rom bsegs)
/\ ART_A Σ' m' /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo (usp + -2128) /\ rt_pres live0 frames0 (usp + -2128) m m'.

Section XRun.
Variables (Σ : rtsA) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word).
Hypothesis HA : ARTc Σ m.
Hypothesis HW : rt_wfx Σ.
Hypothesis HC : rt_count Σ.
Hypothesis HBY : 0x100000 < X16j.qbytes (ql Σ).
Hypothesis FR : qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800)
w0 w1 w2 w3 w4 w5 s6.
Hypothesis ST : stk bsegs m lo (usp + -2208).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x4000 <= usp + -2208.
Hypothesis HSP : usp <= 2 ^ 47.
Hypothesis MI : mem_inv bsegs m.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma xr_geo : geo_ok Σ /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T)
/\ (T + 4096 <= r24 SB \/ r24 SB + 2 ^ 32 <= T) /\ 0 < SB /\ r24 SB + 2 ^ 32 <= l_ACEIL L /\ 2 ^ 44 + SHB <= l_ACEIL L
/\ l_ACEIL L <= 2 ^ 47.
Proof using HW.
clear - HW.
assert (HG : geo_ok Σ) by (destruct HW as (H1 & H2 & _ & H4 & _ & H6 & _); exact (conj H1 (conj H2 (conj H4 H6)))).
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof (dk_T Σ HG) as (T1 & T2 & T3 & T4 & T5).
unfold r24. split; [exact HG|]. repeat split; try lia.
Qed.

Definition xms0 : machine_state :=
MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR) (Z_to_bv 64 (l_T (lay Σ) + 80))
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4a234) fc None m (seg_rom bsegs).

Lemma xr_bytes : 0x100000 < X18y.qbytes (ql Σ) < 2 ^ 63.
Proof using HW HBY.
clear - HW HBY. rewrite <- qbytes_eq. destruct HW as (_ & _ & _ & _ & (Q1 & _) & _). unfold QMAX_L in Q1. lia.
Qed.

Definition xr_dentry (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) : machine_state :=
MS (mkR (Z_to_bv 64 0x4a16c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) a4' a5' a6' a7'
s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 qdrain_entry) fc None m (seg_rom bsegs).

Lemma xr_head : evt bsegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = xr_dentry t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6') xms0.
Proof using HA HW HBY FR ST HLO HLO2 HSP MI.
pose proof (xq_cells Σ m HA) as (QT & _). apply (proj1 (qcache_rep_iff _ _ _)) in QT. destruct QT as (QH & _).
pose proof xr_bytes as HB. pose proof xr_geo as (_ & X1 & X2 & _ & _ & _ & _ & X8 & X9).
assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
unfold xms0. replace (usp + -2208) with (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80) by (rewrite Esp; lia).
eapply evt_mono; [apply (qput_B_drain_spec (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2 s3 s4 s5
a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 s6 ra0 F fc m (T + 80) (T + 208)
(usp + -2056) (X18y.qbytes (ql Σ)) lo _ _ _ QH HB); [| exact MI]|].
- rewrite Esp. replace (usp + -2128 - 80) with (usp + -2208) by lia. exact FR.
- intros ms (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). rewrite Esp. replace (usp + -2128 + -80) with (usp + -2208) by lia.
exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6'. reflexivity.
Qed.

Lemma xr_quar : forall (m2 m3 : mem) G, qcache_rep m2 QG G -> qcache_rep m2 (T + 80) [] -> q_lock m2 0 0 ->
Forall (fun e => r24 SB <= fst e /\ fst e + 8192 <= r24 SB + 2 ^ 32) G ->
munch [(usp + -2208, usp + -2128)] m2 m3 -> wmono bsegs m2 m3 -> quar_rep (set_q Σ [] G) m3.
Proof using HW HLO HLO2.
intros m2 m3 G QG2 QT2 LK2 RG MU WM. pose proof xr_geo as (_ & X1 & X2 & _ & _ & X6 & X7 & X8 & X9). unfold SHB in X8.
unfold quar_rep. cbn [lay ql qg set_q].
split; [apply (qcache_rep_frame _ m2 m3 _ _ QT2 MU WM); [cbn [disjoint_from]; unfold qcacheT; lia | constructor]|].
split; [apply (qcache_rep_frame _ m2 m3 _ _ QG2 MU WM); [cbn [disjoint_from]; lia|];
apply Forall_forall; intros e He; pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2); cbn [disjoint_from]; lia|].
unfold q_lock in LK2. apply (rw_cells_transport bsegs _ m2 m3 _ _ LK2 MU WM). cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
unfold i_q_cmutex, INST, g_instance. lia.
Qed.

Lemma xr_cert : forall bw D, Forall (fun iv => exists c i, In (c, i) D /\ p_abeg SB c i <= fst iv /\ snd iv <= p_abeg SB c i + ClassSize c) bw ->
Forall (dzone Σ D [] [] (TZ_X T) IZ_Q [] lo (usp + -2128)) (W_X T usp bw).
Proof using HLO2.
intros bw D HB. unfold W_X, W_D. rewrite <- !app_assoc. apply Forall_app. split; [|apply Forall_app; split].
- constructor; [left; exists (i_q_cmutex, i_q_cmutex + 4); split; [left; reflexivity | cbn; lia]|].
constructor; [left; exists (i_q_global, i_q_global + 32); split; [right; left; reflexivity | cbn; lia]|].
constructor; [right; left; exists (T + 80, T + 112); split; [left; reflexivity | cbn; lia] | constructor].
- apply Forall_forall. intros iv Hiv. right; right; left. exact (proj1 (Forall_forall _ _) HB iv Hiv).
- constructor; [do 9 right; cbn; lia | constructor; [do 9 right; cbn; lia | constructor]].
Qed.

Lemma xr_TZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_X T)
/\ disjoint_from (TZ_X T) T 0x30 /\ disjoint_from (TZ_X T) (T + 48) 16 /\ disjoint_from (TZ_X T) (T + 0xc60) 1
/\ (forall c, 1 <= c <= 31 -> disjoint_from (TZ_X T) (pc_addr T c) 80).
Proof.
unfold TZ_X. split; [repeat constructor; cbn; lia|]. cbn [disjoint_from]. split; [split; [lia | exact I]|].
split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|]. intros c Hc. unfold pc_addr. split; [lia | exact I].
Qed.

Lemma xr_tail : forall bw D (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem),
(forall c i, In (c, i) D -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch) ->
Forall (fun iv => exists c i, In (c, i) D /\ p_abeg SB c i <= fst iv /\ snd iv <= p_abeg SB c i + ClassSize c) bw ->
munch (W_D T usp bw) m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
qcache_rep m2 QG (qg Σ ++ ql Σ) -> qcache_rep m2 (T + 80) [] -> q_lock m2 0 0 -> stk bsegs m2 lo (usp + -2208) ->
X18y.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
evt bsegs (dpost F fc (set_q Σ [] (qg Σ ++ ql Σ)) gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m)
(MS (mkR (Z_to_bv 64 0x4a16c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc (Z_to_bv 64 0x4a16c)) fc None m2 (seg_rom bsegs)).
Proof using HA HW HC FR ST HLO HLO2 HSP MI.
intros bw D t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 HD HB MU2 WM2 MI2 QG2 QT2 LK2 ST2 HBYg.
pose proof xr_geo as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
rewrite (ret_pc_even 0x4a16c) by (first [reflexivity | lia]).
replace (usp + -2208) with (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80) by (rewrite Esp; lia).

assert (FR2 : qput_frame m2 (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6).
{ rewrite Esp. replace (usp + -2128 - 80) with (usp + -2208) by lia. unfold qput_frame in *.
apply (rw_cells_transport bsegs _ m m2 _ _ FR MU2 WM2). cbn [cells_size csize Nat.add Z.of_nat].
unfold W_D. apply dsj_app; [cbn [disjoint_from]; unfold i_q_cmutex, i_q_global, INST, g_instance; repeat split; lia|].
apply dsj_app; [|cbn [disjoint_from]; repeat split; lia].
apply dsj_forall. apply Forall_forall. intros iv Hiv. destruct (proj1 (Forall_forall _ _) HB iv Hiv) as (c & i & HDi & E1 & E2).
destruct (HD c i HDi) as (-> & Hb). pose proof (dk_slot_in Σ HG 24 i CkBatch ltac:(lia) Hb) as (S1 & S2 & _).
pose proof (dk_geo Σ HG) as (_ & _ & _ & G4 & _ & _ & G7 & _). lia. }
assert (ST2' : stk bsegs m2 lo (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80)) by (rewrite Esp; replace (usp + -2128 - 80) with (usp + -2208) by lia; exact ST2).
eapply evt_mono; [apply (qput_C_spec (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 t3' t4' t5' t6' (Z_to_bv 64 0x4a16c) w0 w1 w2 w3 w4 w5 s6
(Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) F fc m2 lo FR2 ST2'); [rewrite Esp; lia | unfold SEGTOP_A in *; lia | exact MI2]|].
intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
rewrite Esp in MU3, ST3. replace (usp + -2128 - 80) with (usp + -2208) in MU3 by lia.
rewrite (ret_pc_even 0x46800) by (first [reflexivity | lia]).

assert (MU : munch (W_X T usp bw) m m3).
{ apply (munch_trans _ m m2 m3); [apply (munch_weaken (W_D T usp bw)); [|exact MU2] | apply (munch_weaken [(usp + -2208, usp + -2128)]); [|exact MU3]].
- intros x Hx. unfold W_X in Hx. apply (proj1 (X18t.outside_app _ _ _)) in Hx. exact (proj1 Hx).
- intros x Hx. unfold W_X in Hx. apply (proj1 (X18t.outside_app _ _ _)) in Hx. destruct Hx as (_ & Hx). cbn [outside] in Hx |- *. lia. }
assert (WM : wmono bsegs m m3) by exact (wmono_trans bsegs _ _ _ WM2 WM3).
pose proof (xr_cert bw D HB) as CERT. pose proof xr_TZ as (TZ1 & TZ2).
assert (HD' : forall c i, In (c, i) D -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch) by exact HD.
pose proof HW as (_ & _ & HV & _ & _ & _ & _ & Hdep & _).
assert (HQ : quar_rep (set_q Σ [] (qg Σ ++ ql Σ)) m3).
{ apply (xr_quar m2 m3 _ QG2 QT2 LK2); [|exact MU3 | exact WM3].
pose proof (qwf_region _ _ (qwf_of_wfx Σ HW)) as RG. exact RG. }
unfold dpost. exists u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m3. split; [reflexivity|].
split; [apply c_ART; [exact (rt_wf_transfer Σ HW HC ltac:(rewrite qbytes_eq; unfold QMAX_G; lia)) |]
| split; [exact MI3 | split; [exact WM | split; [exact ST3|]]]].
- exact (artc_q Σ m m3 (W_X T usp bw) D (TZ_X T) lo (usp + -2128) [] (qg Σ ++ ql Σ) HG HD' TZ1 TZ2 HLO CERT HA Hdep MU WM HQ).
- exact (client_q Σ m m3 (W_X T usp bw) D (TZ_X T) lo (usp + -2128) HG HD' TZ1 HLO ltac:(clear - HLO2; lia) CERT HV MU).
Qed.

Theorem xfer_evt : X18y.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
evt bsegs (dpost F fc (set_q Σ [] (qg Σ ++ ql Σ)) gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m) xms0.
Proof using HA HW HC HBY FR ST HLO HLO2 HSP MI.
intros HBYg. pose proof xr_geo as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
pose proof (xq_cells Σ m HA) as (QT & QGr & LK & QM).
apply (proj1 (rwc_app bsegs m q_max [C8 (Z_to_bv 64 0x10000000)] [C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)])) in QM.
destruct QM as (QM & _).
pose proof (qwf_of_wfx Σ HW) as WF.
assert (Hne : ql Σ <> []) by (intros E; pose proof HBY as X; rewrite E in X; change (X16j.qbytes []) with 0 in X; lia).
assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
assert (STd : stk bsegs m lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST).
eapply evt_cut; [exact xr_head|]. intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). unfold xr_dentry.
assert (CASE : qg Σ = [] \/ exists pre bl el, qg Σ = pre ++ [(bl, el)]).
{ destruct (qg Σ) as [|b0 rest] eqn:E; [left; reflexivity | right].
destruct (exists_last (l := b0 :: rest) ltac:(discriminate)) as (pre & (bl & el) & E2). exists pre, bl, el. exact E2. }
destruct CASE as [EQG|(pre & bl & el & EQG)].
-
pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYg as HBYg'. rewrite EQG in QGr', WF', HBYg'. cbn [app] in WF', HBYg'.
eapply evt_cut; [apply (qdrain_ret_empty_spec (Z_to_bv 64 0x4a16c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2056) lo (ql Σ) Hne QGr' QT WF' HBYg' LK QM);
try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia); [exact STd | exact MI]|].
intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
rewrite Esp in MU2, ST2.
apply (xr_tail [] [] u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 (fun c i X => False_ind _ X) (Forall_nil _)); try assumption.
+ eapply munch_weaken; [|exact MU2]. unfold W_D, i_q_cmutex, i_q_global, INST, g_instance. cbn [app]. solve_sub_fp.
+ rewrite EQG. exact QG2.
-
pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYg as HBYg'. rewrite EQG in QGr', WF', HBYg'.
assert (Hbl : exists ib, nth_error (r_st (pr Σ 24)) ib = Some CkBatch /\ bl = p_abeg SB 24 ib).
{ destruct HW as (_ & _ & _ & _ & (_ & _ & Q4 & _) & _). rewrite EQG in Q4.
exact (proj1 (Forall_forall _ _) Q4 (bl, el) ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)). }
destruct Hbl as (ib & Hib & Ebl).
eapply evt_cut; [apply (qdrain_ret_app_spec (Z_to_bv 64 0x4a16c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2056) lo pre (ql Σ) bl el Hne QGr' QT WF');
try (rewrite qbytes_app in HBYg'; exact HBYg');
try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
[exact LK | exact QM | exact STd | exact MI]|].
intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
rewrite Esp in MU2, ST2.
apply (xr_tail [(bl, bl + 8)] [(24, ib)] u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2); try assumption.
+ intros c i [E|[]]. injection E as <- <-. split; [reflexivity | exact Hib].
+ constructor; [|constructor]. exists 24, ib. split; [left; reflexivity|]. cbn [fst snd]. rewrite Ebl. change (ClassSize 24) with 8192. lia.
+ eapply munch_weaken; [|exact MU2]. unfold W_D, i_q_cmutex, i_q_global, INST, g_instance. cbn [app]. solve_sub_fp.
+ rewrite EQG. exact QG2.
Qed.

End XRun.

Definition dfinal (F : bvmap 5 word) (fc : bv 32) (Σ : rtsA) (PMc : Model -> Prop) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (m : mem) :
config -> Prop :=
fun cf => exists Σ' : rtsA,
ASTA RTA Σ' PMc (dpost F fc Σ' gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m) cf
/\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ rtA_pois Σ' = rtA_pois Σ.

Theorem drain_xfer : forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11
t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
fdfs_only PMc -> mat_stable PMc ->
ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < X16j.qbytes (ql Σ) ->
qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6 ->
stk bsegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
mem_inv bsegs m ->
X18y.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
cps bsegs (ASTA RTA Σ PMc (eq (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
(dfinal F fc Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
intros Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI HBYg.
intros TT cf Hc0 Hk.
pose proof (xfer_evt Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
w0 w1 w2 w3 w4 w5 s6 HA HW HC HBY FR ST HLO HLO2 HSP MI HBYg) as W1.
lazymatch type of W1 with evt bsegs _ ?X => assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc0).
intros c1 Hc1. apply Hk. exists (set_q Σ [] (qg Σ ++ ql Σ)).
split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. eapply AST_conseq; [exact Hc1| |].
- intros ms P. exact P.
- intros mo (HM & HP). split; [|exact HP]. cbn [ARTM RTA]. apply (artm_eq Σ); [reflexivity | reflexivity | reflexivity | exact HM].
Qed.
End RL_drain_xfer.
Export RL_drain_xfer.

Module RL_drain_rhead.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18d X18y X18t X18s X18j X18w X18x X16j X161 X13v X16p X13t X16b X14p X14t X13u X14q X14r X140 X133 X13c X13a X13g X138 X12t.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer.

Definition bidx (SB b : Z) : nat := Z.to_nat ((b - SB - 24 * 2 ^ 32) / 8192).
Definition bslots (SB : Z) (bs : list batch) : list (Z * nat) := map (fun b => (24, bidx SB (fst b))) bs.

Lemma bidx_abeg : forall SB i, bidx SB (p_abeg SB 24 i) = i.
Proof.
intros SB i. unfold bidx, p_abeg. change (ClassSize 24) with 8192.
replace (SB + 24 * 2 ^ 32 + Z.of_nat i * 8192 - SB - 24 * 2 ^ 32) with (Z.of_nat i * 8192) by lia.
rewrite Z.div_mul by lia. apply Nat2Z.id.
Qed.

Lemma bslots_ok : forall Σ bs, Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) bs ->
forall c i, In (c, i) (bslots (l_SB (lay Σ)) bs) -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch.
Proof.
intros Σ bs HB c i Hin. unfold bslots in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
destruct (proj1 (Forall_forall _ _) HB b Hb) as (j & Hj & Eb). rewrite Eb, bidx_abeg. split; [reflexivity | exact Hj].
Qed.

Lemma bslots_cover : forall Σ bs, Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) bs ->
Forall (fun iv => exists c i, In (c, i) (bslots (l_SB (lay Σ)) bs) /\ p_abeg (l_SB (lay Σ)) c i <= fst iv /\ snd iv <= p_abeg (l_SB (lay Σ)) c i + ClassSize c)
(bivs bs).
Proof.
intros Σ bs HB. apply Forall_forall. intros iv Hiv. unfold bivs in Hiv. apply in_map_iff in Hiv as (b & <- & Hb).
destruct (proj1 (Forall_forall _ _) HB b Hb) as (j & Hj & Eb). exists 24, j. split.
- unfold bslots. apply in_map_iff. exists b. split; [rewrite Eb, bidx_abeg; reflexivity | exact Hb].
- cbn [fst snd]. rewrite Eb. change (ClassSize 24) with 8192. lia.
Qed.

Section RRun.
Variables (Σ : rtsA) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word).
Hypothesis HA : ARTc Σ m.
Hypothesis HW : rt_wfx Σ.
Hypothesis HC : rt_count Σ.
Hypothesis HBY : 0x100000 < X16j.qbytes (ql Σ).
Hypothesis FR : qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800)
w0 w1 w2 w3 w4 w5 s6.
Hypothesis ST : stk bsegs m lo (usp + -2208).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x4000 <= usp + -2208.
Hypothesis HSP : usp <= 2 ^ 47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis HBYr : 0x10000000 < X18y.qbytes (qg Σ ++ ql Σ).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation G := (qg Σ ++ ql Σ).

Definition rh_entry (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x47cac) (Z_to_bv 64 (usp + -2288)) gp (Z_to_bv 64 tpA) t0' t1' t2' s0' s1' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (usp + -2288)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) a4' a5' a6' a7' s2' s3' s4' s5
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 qdorec_entry) fc None m3 (seg_rom bsegs).

Definition rh_post : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word) (m3 : mem),
ms = rh_entry t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' m3
/\ ARTc (set_q Σ [] (rec_r G QMIN)) m3 /\ qcache_rep m3 (usp + -2288) (rec_x G QMIN)
/\ qrec_frame m3 (usp + -2288) (Z_to_bv 64 0x4a16c) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4
/\ qput_frame m3 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6
/\ stk bsegs m3 lo (usp + -2288) /\ mem_inv bsegs m3 /\ wmono bsegs m m3 /\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m3.

Lemma rr_qg : exists pre bl el, qg Σ = pre ++ [(bl, el)].
Proof using HW HBYr.
destruct (qg Σ) as [|b0 rest] eqn:E.
- exfalso. pose proof HW as (_ & _ & _ & _ & (Q1 & _) & _). cbn [app] in HBYr. rewrite <- qbytes_eq in HBYr.
unfold QMAX_L in Q1. lia.
- destruct (exists_last (l := b0 :: rest) ltac:(discriminate)) as (pre & (bl & el) & E2). exists pre, bl, el. exact E2.
Qed.

Definition W_RH (T usp bl : Z) (bs : list batch) : list ivl :=
[(i_q_cmutex, i_q_cmutex + 4); (i_q_global, i_q_global + 32); (T + 80, T + 112); (bl, bl + 8); (usp - 2304, usp - 2208)] ++ bivs bs.

Lemma rr_cert : forall bl, In bl (map fst G) ->
Forall (dzone Σ (bslots SB G) [] [] (TZ_X T) IZ_Q [] lo (usp + -2128)) (W_RH T usp bl G).
Proof using HW HLO2.
intros bl Hbl. pose proof HW as (_ & _ & _ & _ & (_ & _ & Q4 & _) & _).
assert (Q4' : Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg SB 24 i) G)
by (apply (Permutation_Forall (Permutation_app_comm (ql Σ) (qg Σ))); exact Q4).
unfold W_RH. apply Forall_app. split.
- constructor; [left; exists (i_q_cmutex, i_q_cmutex + 4); split; [left; reflexivity | cbn; lia]|].
constructor; [left; exists (i_q_global, i_q_global + 32); split; [right; left; reflexivity | cbn; lia]|].
constructor; [right; left; exists (T + 80, T + 112); split; [left; reflexivity | cbn; lia]|].
constructor.
{ right; right; left. apply in_map_iff in Hbl as (b & E & Hb). destruct (proj1 (Forall_forall _ _) Q4' b Hb) as (j & Hj & Eb).
exists 24, j. split; [unfold bslots; apply in_map_iff; exists b; split; [rewrite Eb, bidx_abeg; reflexivity | exact Hb]|].
cbn [fst snd]. rewrite <- E, Eb. change (ClassSize 24) with 8192. lia. }
constructor; [do 9 right; cbn; lia | constructor].
- apply Forall_forall. intros iv Hiv. right; right; left. exact (proj1 (Forall_forall _ _) (bslots_cover Σ G Q4') iv Hiv).
Qed.

Theorem rr_evt : evt bsegs rh_post (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp).
Proof using HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr.
pose proof (xr_geo Σ HW) as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
pose proof (xq_cells Σ m HA) as (QT & QGr & LK & QM).
apply (proj1 (rwc_app bsegs m q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661)] [C8 (Z_to_bv 64 0x100000)])) in QM.
destruct QM as (QM & _).
pose proof (qwf_of_wfx Σ HW) as WF.
assert (Hne : ql Σ <> []) by (intros E; pose proof HBY as X; rewrite E in X; change (X16j.qbytes []) with 0 in X; lia).
assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
assert (STd : stk bsegs m lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST).
destruct rr_qg as (pre & bl & el & EQG).
assert (Hbl : In bl (map fst G)) by (rewrite EQG; apply in_map_iff; exists (bl, el); split; [reflexivity | apply in_or_app; left; apply in_or_app; right; left; reflexivity]).
eapply evt_cut; [exact (xr_head Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
w0 w1 w2 w3 w4 w5 s6 HA HW HBY FR ST HLO HLO2 HSP MI)|].
intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). unfold xr_dentry.
pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYr as HBYr'. rewrite EQG in QGr', WF', HBYr'.
assert (HBY2 : 0x10000000 < X18y.qbytes (pre ++ [(bl, el)]) + X18y.qbytes (ql Σ) < 2 ^ 56).
{ rewrite <- qbytes_app. split; [exact HBYr'|]. pose proof HW as (_ & _ & _ & _ & (Q1 & Q2 & _) & _).
rewrite <- EQG, qbytes_app, <- !qbytes_eq. unfold QMAX_L, QMAX_G in *. lia. }
eapply evt_cut; [apply (qdrain_rec_app_spec (Z_to_bv 64 0x4a16c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2056) lo pre (ql Σ) bl el Hne QGr' QT WF' HBY2 LK QM);
try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
[exact STd | exact MI]|].
intros ms (u0 & u1 & u2 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
rewrite Esp in MU2, ST2. rewrite <- EQG in QG2.
assert (HBYG : X18y.qbytes G < 2 ^ 56) by (rewrite EQG, qbytes_app; lia).
assert (ST2' : stk bsegs m2 lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST2).
eapply evt_mono; [apply (qrec_A_spec_closed (Z_to_bv 64 0x4a16c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) u0 u1 u2
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) v4 v5 v6 v7 s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
u3 u4 u5 u6 F fc m2 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) QMIN SB lo G QG2 WF HBYG);
try (unfold QMIN; lia); try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
[exact LK2 | exact ST2' | exact MI2]|].
intros ms (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & y3 & y4 & y5 & y6 & m3 & -> & MU3 & WM3 & MI3 & QG3 & TQ3 & LK3 & FR3 & ST3).
rewrite Esp in MU3, ST3, TQ3, FR3. replace (usp + -2208 + -80) with (usp + -2288) in ST3, TQ3, FR3 by lia.
rewrite Esp. replace (usp + -2208 + -80) with (usp + -2288) by lia.
exists y0, y1, y2, z0, z1, z5, z6, z7, z8, z2, z3, z4, y3, y4, y5, y6, m3. split; [reflexivity|].

assert (MU : munch (W_RH T usp bl G) m m3).
{ apply (munch_trans _ m m2 m3).
- eapply munch_weaken; [|exact MU2]. intros x Hx. unfold W_RH in Hx. apply (proj1 (X18t.outside_app _ _ _)) in Hx. destruct Hx as (Hx & _).
cbn [outside] in Hx |- *. unfold i_q_cmutex, i_q_global, INST, g_instance in *. lia.
- eapply munch_weaken; [|exact MU3]. intros x Hx. unfold W_RH in Hx. apply (proj1 (X18t.outside_app _ _ _)) in Hx. destruct Hx as (Hx & Hb).
apply (proj2 (X18t.outside_app _ _ _)). split; [|exact Hb].
cbn [outside] in Hx |- *. unfold i_q_cmutex, i_q_global, INST, g_instance in *. lia. }
assert (WM : wmono bsegs m m3) by exact (wmono_trans bsegs _ _ _ WM2 WM3).
pose proof (rr_cert bl Hbl) as CERT. pose proof (xr_TZ Σ) as (TZ1 & TZ2).
pose proof HW as (_ & _ & HV & _ & (_ & _ & Q4 & _) & _ & _ & Hdep & _).
assert (Q4' : Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg SB 24 i) G)
by (apply (Permutation_Forall (Permutation_app_comm (ql Σ) (qg Σ))); exact Q4).
pose proof (bslots_ok Σ G Q4') as HD.
assert (HQ : quar_rep (set_q Σ [] (rec_r G QMIN)) m3).
{ unfold quar_rep. cbn [lay ql qg set_q]. split; [|split; [exact QG3 | exact LK3]].
apply (qcache_rep_frame _ m2 m3 _ _ QT2 MU3 WM3); [|constructor].
apply disjoint_from_app; [cbn [disjoint_from]; unfold qcacheT; unfold SEGTOP_A in *; repeat split; lia|].
apply disjoint_bivs. apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Q4' e He) as (j & Hj & Ej).
pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). pose proof (dk_T Σ HG) as (_ & _ & _ & _ & T5).
pose proof (dk_geo Σ HG) as (_ & _ & _ & _ & _ & G6 & G7 & _). rewrite Ej. unfold qcacheT. change (ClassSize 24) with 8192 in *. lia. }
split; [exact (artc_q Σ m m3 (W_RH T usp bl G) (bslots SB G) (TZ_X T) lo (usp + -2128) [] (rec_r G QMIN) HG HD TZ1 TZ2 HLO CERT HA Hdep MU WM HQ)|].
split; [exact TQ3|]. split; [exact FR3|].
split.
{ unfold qput_frame in *. apply (rw_cells_transport bsegs _ m m3 _ _ FR MU WM). cbn [cells_size csize Nat.add Z.of_nat].
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
unfold W_RH. apply disjoint_from_app.
- apply in_map_iff in Hbl as (b & Eb & Hb). destruct (proj1 (Forall_forall _ _) Q4' b Hb) as (j & Hj & Ej).
pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). rewrite <- Eb, Ej.
cbn [disjoint_from]. unfold i_q_cmutex, i_q_global, INST, g_instance. change (ClassSize 24) with 8192 in *. unfold SHB in G1.
repeat split; lia.
- apply disjoint_bivs. apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Q4' e He) as (j & Hj & Ej).
pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). rewrite Ej. change (ClassSize 24) with 8192 in *. lia. }
split; [exact ST3|]. split; [exact MI3|]. split; [exact WM|].
exact (client_q Σ m m3 (W_RH T usp bl G) (bslots SB G) (TZ_X T) lo (usp + -2128) HG HD TZ1 HLO ltac:(clear - HLO2; lia) CERT HV MU).
Qed.

End RRun.
End RL_drain_rhead.
Export RL_drain_rhead.

Module RL_dsec_defs.
Import X12c X0j9 X14x X0j1 X173 X18c X17w X19m X196 X17a X18y X18t X18w X18i X18g X187 X16j X161 X14q X133.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead.

Section Cuts.
Variables (p : dlp) (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat) (s : secst).
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

Definition ds_loopmem (m : mem) : Prop :=
(exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G)
/\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
/\ drec_frame m C j (T + 208) (usp - 2056) (Z_to_bv 64 0x47cac) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
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
End RL_dsec_defs.
Export RL_dsec_defs.

Module RL_dsec_runA.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18w X18i X18g X196 X19j X18h X17i X187 X19g X19i X19h X16j X161 X13v X16p X16b X14p X14t X13u X14q X13w X13x X15m X133 X13c X13a X138 X135 X13d X13m X13o X13n X13j.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead RL_dsec_defs.

Lemma outside_incl : forall W1 W2 x, (forall iv, In iv W1 -> In iv W2) -> outside W2 x -> outside W1 x.
Proof.
intros W1 W2 x HI H. apply outside_Forall. apply Forall_forall. intros iv Hiv.
exact (proj1 (Forall_forall _ _) (proj1 (outside_Forall W2 x) H) iv (HI iv Hiv)).
Qed.

Section RunA.
Variables (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat)
(s : secst) (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word).
Hypothesis HOK : dl_ok p.
Hypothesis HWP : rt_wfP Σk ((b, skipn i ents) :: rest).
Hypothesis HS : dl_sig p Σk.
Hypothesis Hk : nth_error (sec Σk) k = Some s.
Hypothesis Hq : s_quar s = true.
Hypothesis DM : dl_mem p j Σk rest m.
Hypothesis QB : qbatch m b (qfirst rest) ents.
Hypothesis Hib : nth_error (r_st (pr Σk 24)) ib = Some CkBatch.
Hypothesis Eb : b = p_abeg (l_SB (lay Σk)) 24 ib.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation L := (lay Σk).
#[local] Notation T := (l_T (lay Σk)).
#[local] Notation TCX := (l_TCX (lay Σk)).
#[local] Notation SB := (l_SB (lay Σk)).
#[local] Notation PAB := (l_PAB (lay Σk)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).
#[local] Notation n := (s_n s).
#[local] Notation M := (s_mb s + 6128).
#[local] Notation NS := (length (sec Σk)).

Definition ds_ms : machine_state :=
MS (mkR (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
(Z_to_bv 64 (C - 104)) (Z_to_bv 64 M) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom bsegs).

Definition svc_mad : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (mA : mem) (ws : list word) (lst : secst) (muw mudw : word),
ms = MSsvc (sd_M_regs (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' MB MSZ a4' a5' a6' (Z_to_bv 64 1058568)
(Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6')
(dl_F p) (Z_to_bv 64 madv_ecall) (Z_to_bv 64 233) (dl_fc p) None mA (seg_rom bsegs)
/\ munch (qcbrec_sec_W T (C - 112) ++ sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) m mA /\ wmono bsegs m mA
/\ mem_inv bsegs mA
/\ sd_mid (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x47f68) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1057944) MB MSZ
(needed n + rz_size n) TCX T lo muw mudw mA
/\ sd_K1 MB MSZ PAB 0x4000 (Z.of_nat NS) (Z.of_nat k) (s_mb lst) ws mA
/\ Z.of_nat (length ws) = 0x4000 /\ firstn NS ws = map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)
/\ nth_error (sec Σk) (NS - 1) = Some lst.

Lemma ds_run1 : evt bsegs svc_mad ds_ms.
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof (dg_ok Σk HG) as (HT & HSB & TSEP).
pose proof HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
pose proof (dg_consts L m A1) as (IC & MMG & TC & PS & STS & UB). destruct IC as (IC1 & IC2).

pose proof HG as (HL & HR & HSW & HFW).
pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & G2 & G3 & G4 & G5) & GP & GF & GS).
pose proof (nth_error_lt _ _ _ Hk) as Hkl.
assert (Hnres : sec_nres Σk = 0x4000) by (apply SW3; intros E; rewrite E in Hk; destruct k; discriminate).
pose proof (smsz_big n ltac:(lia)) as Hbig.

pose proof A5 as (SC & SPD & (ws & WS & Hwsl & Hwsf) & SPG & SRG & SJK & NMC).
rewrite Hnres in SC, Hwsl.
assert (HIN : firstn NS (map bv_unsigned ws) = map s_mb (sec Σk)).
{ rewrite firstn_map, Hwsf, map_map. apply map_ext_in. intros x Hx. apply unsigned_lit.
pose proof (proj1 (Forall_forall _ _) SW4 x Hx) as ((Y1 & _) & (X1 & _ & X3 & _) & _). pose proof (smsz_pos (s_n x) Y1).
pose proof (dk_geo Σk HG) as (_ & X & _). lia. }

pose proof A4 as (_ & CS). pose proof (CS k s Hk) as X. unfold schunk in X. rewrite Hq in X.
replace (s_mb s + 4096 + 2032) with M in X by lia. replace (s_mb s + 4096 + 2048) with (M + 16) in X by lia.
destruct X as (SHD & WRM & LCH & (b1 & ctx & fid & Hb1 & QH) & STSH & SB1 & SB2 & SB3).
apply (proj1 (rwc_app bsegs m _ [C1 (Z_to_bv 8 3); C1 b1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] [C8 ctx; C8 fid])) in QH.
destruct QH as (QH & QH2).
assert (Hb1r : 0 <= bv_unsigned b1 < 256) by (pose proof (bv_unsigned_in_range 8 b1) as X; unfold bv_modulus in X; cbn in X; lia).
rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b1) in QH.

destruct (fl_two_c8 m (T + 2840) ltac:(apply (stk_within m _ _ _ _ STS); [lia | lia | pose proof HT as (X & _); lia])) as (rfw & rfdw & STW).
rewrite <- (Z_to_bv_bv_unsigned rfw), <- (Z_to_bv_bv_unsigned rfdw) in STW.
pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
pose proof (g_grant Σk HG PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (PA1 & PA2 & PA3 & PA4 & PA5).
pose proof (g_apart Σk HG 1 2 _ _ ltac:(lia) eq_refl eq_refl) as AP12. cbn [fst snd] in AP12. unfold apart in AP12.
pose proof (proj1 (Forall_forall _ _) GS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as AMT.
cbn [fst snd] in AMT. unfold apart in GP, AMT.
assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
eapply evt_cut.
{ unfold ds_ms.
apply (qcbrec_sec_spec (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL L) SB PAB 0x4000 (Z.of_nat NS) ws MB MSZ
(needed n + rz_size n) (Z.of_nat k) M n (bv_unsigned b1) TCX T (bv_unsigned rfw) (bv_unsigned rfdw) (C - 104) lo);
rewrite ?RSP.
all: try assumption.
- split; [exact SPG|]. split; [exact SC|]. split; [exact SPD|]. split; [exact WS | exact SHD].
- rewrite Hwsl. clear - PA3 HLk. lia.
- unfold hide, img_hull_lo, img_hull_hi. rewrite Hwsl. clear - PA5. unfold SEGTOP_A in *. lia.
- rewrite Hwsl. clear - Hkl SW1. unfold SEC_MAX in *. lia.
- rewrite Nat2Z.id, HIN. apply in_map. exact (nth_error_In _ _ Hk).
- rewrite Nat2Z.id, HIN. apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (x & <- & Hx). intros Hle.
destruct (In_nth_error _ _ Hx) as (jx & Hjx). destruct (Nat.eq_dec jx k) as [->|Hne].
+ rewrite Hk in Hjx. injection Hjx as <-. lia.
+ pose proof (SW5 jx k x s Hjx Hk Hne) as AX. unfold apart in AX.
pose proof (proj1 (Forall_forall _ _) SW4 x Hx) as ((Y1 & _) & _). pose proof (smsz_pos (s_n x) Y1). clear - AX Hle Hbig H Hn1. lia.
- clear - G3 HLk. lia.
- clear; lia.
- clear - Hbig Hn1. lia.
- unfold hide. clear - GP GG6 GG7. lia.
- clear - Hn1 Hn2. lia.
- apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
exact (proj1 IC1).
- unfold hide. rewrite Hwsl. clear - AP12. lia.
- clear - N5. lia.
- clear - N6. lia. }
intros ms1 P1.
destruct P1 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m1 & -> & MU1 & WM1 & MI1 & K1 & ST1).
destruct K1 as ((PG1 & SC1 & PD1 & WS1 & SHD1) & HD1 & STW1).
rewrite RSP in MU1, ST1.

assert (HTZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_ST T)) by (unfold TZ_ST; repeat constructor; cbn; lia).
assert (HTZd : disjoint_from (TZ_ST T) T 0x30 /\ disjoint_from (TZ_ST T) (T + 48) 16 /\ disjoint_from (TZ_ST T) (T + 0xc60) 1
/\ (forall c', 1 <= c' <= 31 -> disjoint_from (TZ_ST T) (pc_addr T c') 80) /\ disjoint_from (TZ_ST T) (qcacheT T) 32).
{ unfold TZ_ST, pc_addr, qcacheT. cbn [disjoint_from]. split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|].
split; [split; [lia | exact I]|]. split; [intros c' Hc'; split; [lia | exact I] | split; [lia | exact I]]. }
assert (CERT1 : Forall (dzoneP Σk [] [] [k; (NS - 1)%nat] (TZ_ST T) IZ_S [] lo (C - 112)) (qcbrec_sec_W T (C - 112))).
{ unfold qcbrec_sec_W. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; lia].
- right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; lia].
- do 9 right. left. cbn. lia. }
pose proof (da_consts Σk m m1 _ k (TZ_ST T) lo (C - 112) HG HTZ HTZd HLk CERT1 HA MU1 WM1) as CR1.
pose proof (dg_consts L m1 CR1) as (IC1' & MMG1 & TC1 & PS1 & STS1 & UB1).
pose proof (ds_rel L m1 CR1) as REL1.

destruct (nth_error (sec Σk) (NS - 1)) as [lst|] eqn:Hlst; [|apply nth_error_None in Hlst; lia].
pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
pose proof (smsz_big (s_n lst) ltac:(lia)) as Lbig.
pose proof (CS _ lst Hlst) as X. unfold schunk, shdr in X. destruct X as (LSHD & _).
apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 (s_mb lst)); C8 (Z_to_bv 64 (smsz (s_n lst))); C8 (Z_to_bv 64 (needed (s_n lst) + rz_size (s_n lst)))]
[C8 (Z_to_bv 64 (Z.of_nat (NS - 1)))])) in LSHD.
destruct LSHD as (_ & LIDX). cbn [cells_size csize Nat.add Z.of_nat] in LIDX.

pose proof (g_grant Σk HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
pose proof (g_grant Σk HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (Y1 & Y2 & Y3 & Y4 & Y5).
pose proof (g_apart Σk HG 1 3 _ _ ltac:(lia) eq_refl eq_refl) as AP13. pose proof (g_apart Σk HG 2 3 _ _ ltac:(lia) eq_refl eq_refl) as AP23.
cbn [fst snd] in AP13, AP23. unfold apart in AP13, AP23.
pose proof (proj1 (Forall_forall _ _) GS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as AMP.
pose proof (proj1 (Forall_forall _ _) GS (TCX, 0x10000) ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as AMX.
pose proof (proj1 (Forall_forall _ _) LGS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as ALP.
pose proof (proj1 (Forall_forall _ _) LGS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as ALT.
pose proof (proj1 (Forall_forall _ _) LGS (TCX, 0x10000) ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as ALX.
cbn [fst snd] in AMP, AMX, ALP, ALT, ALX. unfold apart in AMP, AMX, ALP, ALT, ALX.
assert (ALM : s_mb lst = MB \/ s_mb lst + 32 <= MB \/ MB + MSZ <= s_mb lst).
{ destruct (Nat.eq_dec (NS - 1) k) as [E|E].
- left. rewrite E in Hlst. rewrite Hk in Hlst. injection Hlst as <-. reflexivity.
- pose proof (SW5 (NS - 1)%nat k lst s Hlst Hk E) as A. unfold apart in A. clear - A Lbig Ln1. lia. }

assert (HWI : nth_error ws k = Some (Z_to_bv 64 MB)).
{ assert (E : nth_error (firstn NS ws) k = nth_error (map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)) k) by (rewrite Hwsf; reflexivity).
rewrite nth_error_firstn, nth_error_map, Hk in E. destruct (Nat.ltb_spec k NS); [exact E | lia]. }
assert (HWL : nth_error ws (NS - 1) = Some (Z_to_bv 64 (s_mb lst))).
{ assert (E : nth_error (firstn NS ws) (NS - 1) = nth_error (map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)) (NS - 1)) by (rewrite Hwsf; reflexivity).
rewrite nth_error_firstn, nth_error_map, Hlst in E. destruct (Nat.ltb_spec (NS - 1) NS); [exact E | lia]. }

destruct (fl_two_c8 m1 (T + 2888) ltac:(apply (stk_within m1 _ _ _ _ STS1); [lia | lia | pose proof HT as (X & _); lia])) as (muw & mudw & MUW).
assert (MB8 : MB mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
assert (MSZ8 : MSZ mod 8 = 0).
{ unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed n + rz_size n + 4095) / 4096) * 512 + 512). lia. }
assert (ESH : shad (MB + MSZ) = shad MB + MSZ / 8) by (apply shad_add8'; assumption).
destruct (stk_CB m1 (shad MB) (MSZ / 8) ltac:(rewrite <- ESH; exact (stk_wmono m m1 _ _ STSH WM1)) ltac:(apply Z.div_pos; lia)) as (shj & SHJ).
assert (LIDX1 : rw_cells bsegs m1 (s_mb lst + 24) [C8 (Z_to_bv 64 (Z.of_nat (NS - 1)))]).
{ apply (rw_cells_transport bsegs _ m m1 _ _ LIDX MU1 WM1). unfold qcbrec_sec_W. cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
unfold i_sec_mutex, INST, g_instance. clear - LG1 LG3 LG5 ALT HLk N5 Lbig Ln1. unfold img_hull_lo, img_hull_hi, SEGTOP_A in *.
repeat split; try exact I; lia. }
assert (SJ1 : sec_junk m1).
{ destruct SJK as ((bj & jj & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)).
unfold qcbrec_sec_W in MU1. unfold i_sec_sorted, i_sec_bylog, i_gstat_alloc, i_sec_mutex, INST, g_instance in *.
split; [exists bj, jj, w1, w2, w3, w4; apply (rw_cells_transport bsegs _ m m1 _ _ J1 MU1 WM1); cbn [disjoint_from cells_size csize Nat.add Z.of_nat];
clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia|].
split; [exists bl; split; [exact Hbl|]; apply (u64arr_transport bsegs _ m m1 _ _ J2 MU1 WM1); rewrite Hbl; cbn [disjoint_from Z.of_nat];
clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia|].
exists ga, gm. apply (rw_cells_transport bsegs _ m m1 _ _ J3 MU1 WM1); cbn [disjoint_from cells_size csize Nat.add Z.of_nat];
clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia. }
apply (proj1 (rwc_app bsegs m1 _ [C8 (Z_to_bv 64 MB); C8 (Z_to_bv 64 MSZ); C8 (Z_to_bv 64 (needed n + rz_size n))]
[C8 (Z_to_bv 64 (Z.of_nat k))])) in SHD1.
destruct SHD1 as (HDA & HDI). cbn [cells_size csize Nat.add Z.of_nat] in HDI.
eapply evt_cut.
{ apply (secdealloc_A1_spec (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) u0 u1 u2 (Z_to_bv 64 C) (Z_to_bv 64 INST) u3 u4 u5 u6 u7
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) u8 u9 u10 u11 (dl_F p) (dl_fc p) m1 MB MSZ (needed n + rz_size n) (Z.of_nat k) PAB 0x4000 (Z.of_nat NS)
(s_mb lst) (Z.of_nat (NS - 1)) TCX T lo ws muw mudw shj); rewrite ?RSP.
all: try assumption.
- split; [exact G2|]. split; [clear - Hbig Hn1; lia|].
unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed n + rz_size n + 4095) / 4096) + 1). lia.
- unfold gobj. clear - G1 G3 G4 G5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - PA1 PA3 PA4 PA5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - Y1 Y3 Y4 Y5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - X1 X3 X4 X5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- clear - LG1 LG3 LG4 LG5 HLk Lbig Ln1. unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold sapart. clear - ALP Lbig Ln1. lia.
- unfold sapart. clear - AMX. lia.
- unfold sapart. clear - AP23. lia.
- unfold sapart. clear - AP12. lia.
- unfold sapart. clear - AP13. lia.
- unfold sapart. clear - ALT Lbig Ln1. lia.
- unfold sapart. clear - ALX Lbig Ln1. lia.
- clear - Hkl SW1 Hwsl. unfold SEC_MAX in *. lia.
- rewrite Nat2Z.id. exact HWI.
- replace (Z.to_nat (Z.of_nat NS - 1)) with (NS - 1)%nat by (clear - Hkl; lia). exact HWL.
- clear - HSB HLk. destruct HSB as (? & _ & ? & _). unfold kHighShadowEnd in *. lia.
- clear - N5. lia.
- clear - N6. lia. }
intros ms2 P2.
destruct P2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & m2 & -> & MU2 & WM2 & MI2 & MID2 & K2).
rewrite RSP in MU2.
apply evt_done. unfold svc_mad.
exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, m2, ws, lst, muw, mudw.
split; [reflexivity|].
split.
{ apply (munch_trans _ m m1 m2).
- apply (munch_weaken (qcbrec_sec_W T (C - 112)) _ m m1); [|exact MU1]. intros x Hx. apply outside_app_inv in Hx. exact (proj1 Hx).
- apply (munch_weaken (sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) _ m1 m2); [|exact MU2]. intros x Hx.
apply outside_app_inv in Hx. exact (proj2 Hx). }
split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact MID2|]. split; [exact K2|].
split; [exact Hwsl|]. split; [exact Hwsf | exact Hlst].
Qed.

Lemma ds_fin : forall (W0 : list ivl) (lst : secst) (ws : list word) (m2 : mem) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw : word),
nth_error (sec Σk) (NS - 1) = Some lst -> Z.of_nat (length ws) = 0x4000 ->
firstn NS ws = map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk) ->
munch (W0 ++ [(s_mb lst + 24, s_mb lst + 32)]) m m2 -> wmono bsegs m m2 ->
Forall (dzoneP Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112)) W0 ->
sd_K MB MSZ (needed n + rz_size n) PAB 0x4000 (Z.of_nat NS) (Z.of_nat k) (s_mb lst) T ws muw mudw m2 ->
mem_inv bsegs m2 -> uod_frame m2 (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x47f68) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1057944) ->
stk bsegs m2 lo (C - 112 - 48) ->
svc_mun p j b ents i rest Σk k s
(MSsvc (uod_regs (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) v0 v1 v2 MB MSZ v3 v4 v5 v6 v7
(Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) v8 v9 v10 v11)
(dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) (dl_fc p) None m2 (seg_rom bsegs)).
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
intros W0 lst ws m2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw Hlst Hwsl Hwsf MU WM CERT0 K2 MI2 UF2 ST2.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof HG as (HL & HR & HSW & HFW).
pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
pose proof (nth_error_lt _ _ _ Hk) as Hkl.
assert (Hnres : sec_nres Σk = 0x4000) by (apply SW3; intros E; rewrite E in Hk; destruct k; discriminate).
pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
pose proof (smsz_big (s_n lst) ltac:(clear - Ln1; lia)) as Lbig.
pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
assert (HTZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_ST T)) by (unfold TZ_ST; repeat constructor; cbn; lia).
assert (HTZd : disjoint_from (TZ_ST T) T 0x30 /\ disjoint_from (TZ_ST T) (T + 48) 16 /\ disjoint_from (TZ_ST T) (T + 0xc60) 1
/\ (forall c', 1 <= c' <= 31 -> disjoint_from (TZ_ST T) (pc_addr T c') 80) /\ disjoint_from (TZ_ST T) (qcacheT T) 32).
{ unfold TZ_ST, pc_addr, qcacheT. cbn [disjoint_from]. split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|].
split; [split; [lia | exact I]|]. split; [intros c' Hc'; split; [lia | exact I] | split; [lia | exact I]]. }
destruct K2 as (SCK & PDK & SJK2 & WSK & LIK & _). rewrite Nat2Z.id in WSK.
set (LC := [(s_mb lst + 24, s_mb lst + 32)]) in *.
assert (HQB : Forall (fun b0 => exists j0, nth_error (r_st (pr Σk 24)) j0 = Some CkBatch /\ fst b0 = p_abeg (l_SB (lay Σk)) 24 j0) (ql Σk ++ qg Σk))
by exact (hqb_of_wfP _ _ HWP).
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
assert (CERT : Forall (dzoneP Σk [] [] [k; (NS - 1)%nat] (TZ_ST T) IZ_S [] lo (C - 112)) (W0 ++ LC)).
{ apply Forall_app. split; [apply (dzoneP_mono_DS _ _ _ [k]); [intros x [E|[]]; left; exact E | exact CERT0]|].
apply Forall_cons; [|apply Forall_nil]. do 7 right. left. exists (NS - 1)%nat, lst. split; [right; left; reflexivity|].
split; [exact Hlst|]. cbn [fst snd]. clear - Lbig Ln1. lia. }

assert (LCS : forall a n0, l_ACEIL L <= a -> disjoint_from LC a n0).
{ intros a n0 Ha. unfold LC. cbn [disjoint_from]. split; [|exact I]. clear - Ha LG3 Lbig Ln1. lia. }
assert (STK_AV : forall a n0, C - 112 <= a -> a + n0 <= USTACK_TOP -> disjoint_from (W0 ++ LC) a n0).
{ intros a n0 H1 H2. apply dsj_app; [|apply LCS; clear - H1 HLk N5; lia].
exact (dp_stack_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk ltac:(clear - N5; lia) W0 CERT0 a n0 H1 H2). }
assert (SLOT_AV : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from (W0 ++ LC) (p_abeg SB 24 j') 8192).
{ intros j' Hj'. pose proof (dp_slot_in Σk HG 24 j' _ ltac:(clear; lia) Hj') as (S1 & S2 & _). change (ClassSize 24) with 8192 in S1, S2 |- *.
apply dsj_app.
- exact (dp_slot_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0 24 j' CkBatch (p_abeg SB 24 j') 8192
ltac:(clear; lia) Hj' ltac:(intros []) ltac:(clear; lia) ltac:(change (ClassSize 24) with 8192; clear; lia)).
- unfold LC. cbn [disjoint_from]. split; [|exact I]. clear - S1 S2 LGP GG7 Lbig Ln1. unfold apart in LGP. lia. }
unfold svc_mun. exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, m2. split; [reflexivity|].
split.
{
apply (ds_artc Σk m m2 (W0 ++ LC) k s lst (TZ_ST T) lo (C - 112) ws HG Hk Hlst HTZ HTZd HLk CERT HA Hdep HQB MU WM).
- rewrite Hnres. exact SCK.
- exact PDK. - exact SJK2. - exact WSK. - rewrite Hnres. exact Hwsl. - exact Hwsf.
- intros Hlt. split; [|exact LIK].
assert (HnIn : ~ In (NS - 1)%nat [k]) by (intros [E|[]]; clear - E Hlt; lia).
pose proof (kw_schunk Σk W0 [k] HG
(dp_shad_app_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0)
(dp_secmap_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0)
(NS - 1)%nat lst Hlst HnIn) as (LA1 & LA2 & LA3 & LA4 & LA5 & LA6).
assert (LSH : forall a n0, 0 <= n0 -> shad (s_mb lst) <= a -> a + n0 <= shad (s_mb lst + smsz (s_n lst)) -> disjoint_from LC a n0).
{ intros a n0 H0 H1 H2. unfold LC. cbn [disjoint_from]. split; [|exact I].
pose proof (dp_shad_rng (s_mb lst) ltac:(lia)). pose proof (dp_shad_rng (s_mb lst + smsz (s_n lst)) ltac:(lia)).
clear - H0 H1 H2 H H3 LG4 Lbig Ln1. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia. }
pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 4096 + 2048) ltac:(lia)) as Q1.
pose proof (fk_map Σk HG _ lst Hlst) as (_ & _ & _ & _ & _ & _ & _ & LRoom & LRu & _).
assert (Hru : 8 <= ru8 (s_n lst) /\ s_n lst <= ru8 (s_n lst) /\ 6144 + ru8 (s_n lst) <= smsz (s_n lst)).
{ split; [|split; [exact LRu | exact LRoom]]. unfold ru8.
assert (X : 1 <= (s_n lst + 7) / 8) by (apply Z.div_le_lower_bound; clear - Ln1; lia). clear - X; lia. }
unfold schunk_avoid_nh. split; [|split; [|split; [|split; [|split]]]].
+ apply dsj_app; [apply (dsj_sub W0 (s_mb lst) 32); [exact LA1 | clear; lia | clear; lia]|]. unfold LC. cbn [disjoint_from]. split; [clear; lia | exact I].
+ apply dsj_app; [exact LA2|]. unfold LC. cbn [disjoint_from]. split; [clear; lia | exact I].
+ apply dsj_app; [exact LA3|]. unfold LC. cbn [disjoint_from]. split; [|exact I]. destruct (s_quar lst); clear; lia.
+ apply dsj_app; [exact LA4|]. apply LSH; [clear; lia | clear; lia|]. change ((4096 + 2048) / 8) with 768. rewrite Z.max_r by (clear; lia).
pose proof (fk_shad_le2 (s_mb lst) 6144 ltac:(clear - LG1; lia) ltac:(clear; lia)) as LX1.
pose proof (dp_shad_mono (s_mb lst + 6144) (s_mb lst + smsz (s_n lst)) ltac:(clear - Hru; lia)) as LX2. change (6144 / 8) with 768 in LX1. clear - LX1 LX2. lia.
+ apply dsj_app; [exact LA5|]. destruct Hru as (U1 & U2 & U3).
pose proof (fk_shad_le2 (s_mb lst + 6144) (ru8 (s_n lst)) ltac:(clear - LG1; lia) ltac:(clear - U1; lia)) as E2.
pose proof (dp_shad_mono (s_mb lst + 6144 + ru8 (s_n lst)) (s_mb lst + smsz (s_n lst)) ltac:(clear - U3; lia)) as E4.
pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 6144) ltac:(clear; lia)) as E5.
assert (E7 : 0 <= ru8 (s_n lst) / 8) by (apply Z.div_pos; clear - U1; lia).
replace (s_mb lst + 4096 + 2048) with (s_mb lst + 6144) by (clear; ring).
apply LSH; [clear; lia | exact E5|].
destruct (s_quar lst); [rewrite fdrun_lenZ by exact E7 | rewrite (fl_ushadow_len (s_n lst)) by (clear - Ln1; lia)]; clear - E2 E4; lia.
+ apply dsj_app; [exact LA6|]. destruct Hru as (U1 & U2 & U3).
pose proof (fk_shad_le2 (s_mb lst + 6144 + ru8 (s_n lst)) (smsz (s_n lst) - 6144 - ru8 (s_n lst)) ltac:(clear - LG1 U1; lia) ltac:(clear - U3; lia)) as E3.
replace (s_mb lst + 6144 + ru8 (s_n lst) + (smsz (s_n lst) - 6144 - ru8 (s_n lst))) with (s_mb lst + smsz (s_n lst)) in E3 by (clear; ring).
pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 6144 + ru8 (s_n lst)) ltac:(clear - U1; lia)) as E6.
assert (E8 : 0 <= (smsz (s_n lst) - 6144 - ru8 (s_n lst)) / 8) by (apply Z.div_pos; clear - U3; lia).
replace (s_mb lst + 4096 + 2048 + ru8 (s_n lst)) with (s_mb lst + 6144 + ru8 (s_n lst)) by (clear; ring).
replace (smsz (s_n lst) - 4096 - 2048 - ru8 (s_n lst)) with (smsz (s_n lst) - 6144 - ru8 (s_n lst)) by (clear; ring).
rewrite Z.max_r by exact E8.
apply LSH; [exact E8 | exact E6 | clear - E3; lia]. }
split; [exact MI2|]. split; [exact UF2|]. split; [exact ST2|].

split.
{ destruct WM0 as (G & WG & HGo). exists G. split; [exact (wmono_out_wmono G _ m m2 WG WM) | exact HGo]. }
split.
{ apply (rt_pres_trans _ _ _ _ m m2 RP). intros a Ha. apply MU.
rewrite <- Elv, <- Efr in Ha.
apply (ds_client Σk W0 k s lst (TZ_ST T) lo (C - 112) HG Hk Hq (nth_error_In _ _ Hlst) HTZ HLk ltac:(lia) CERT0 Hlive).
destruct Ha as [Ha|Ha]; [left; clear - Ha; lia | right; exact Ha]. }
pose proof FR as (FR1 & FR2 & FR3).
split.
{ split; [|split].
- apply (rw_cells_transport bsegs _ m m2 _ _ FR1 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia.
- apply (rw_cells_transport bsegs _ m m2 _ _ FR2 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia.
- apply (rw_cells_transport bsegs _ m m2 _ _ FR3 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia. }
split.
{ apply (qcache_rep_frame _ m m2 C rest QR MU WM); [apply STK_AV; clear - N6; unfold USTACK_TOP; lia|].
apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (SLOT_AV j' Hj'). }
apply (qbatch_frame _ m m2 b (qfirst rest) ents QB MU WM). rewrite Eb. exact (SLOT_AV ib Hib).
Qed.

Definition mad_eff : SyscallEffect :=
mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 (pbeg (shad MB)), Z_to_bv 64 (pend (shad (MB + MSZ)) - pbeg (shad MB)))].

Lemma ds_run2 : forall ms0, svc_mad ms0 -> evt bsegs (svc_mun p j b ents i rest Σk k s) (nretA ms0 mad_eff).
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & mA & ws & lst & muw & mudw
& -> & MU1 & WM1 & MI1 & MID & K1 & Hwsl & Hwsf & Hlst).
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof (dg_ok Σk HG) as (HT & HSB & TSEP).
pose proof HG as (HL & HR & HSW & HFW).
pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & G2 & G3 & G4 & G5) & GP & GF & GS).
pose proof (nth_error_lt _ _ _ Hk) as Hkl.
pose proof (smsz_big n ltac:(clear - Hn1; lia)) as Hbig.
pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
pose proof (smsz_big (s_n lst) ltac:(clear - Ln1; lia)) as Lbig.
pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
pose proof (g_grant Σk HG PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (PA1 & PA2 & PA3 & PA4 & PA5).
pose proof (g_grant Σk HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
pose proof (g_grant Σk HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (Y1 & Y2 & Y3 & Y4 & Y5).
pose proof (g_apart Σk HG 1 2 _ _ ltac:(clear; lia) eq_refl eq_refl) as AP12. pose proof (g_apart Σk HG 2 3 _ _ ltac:(clear; lia) eq_refl eq_refl) as AP23.
cbn [fst snd] in AP12, AP23. unfold apart in AP12, AP23.
pose proof (proj1 (Forall_forall _ _) GS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as AMP.
pose proof (proj1 (Forall_forall _ _) GS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as AMT.
pose proof (proj1 (Forall_forall _ _) LGS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as ALT.
cbn [fst snd] in AMP, AMT, ALT. unfold apart in AMP, AMT, ALT, GP.
assert (ALM : s_mb lst = MB \/ s_mb lst + 32 <= MB \/ MB + MSZ <= s_mb lst).
{ destruct (Nat.eq_dec (NS - 1) k) as [E|E].
- left. rewrite E in Hlst. rewrite Hk in Hlst. injection Hlst as <-. reflexivity.
- pose proof (SW5 (NS - 1)%nat k lst s Hlst Hk E) as A. unfold apart in A. clear - A Lbig Ln1. lia. }
assert (MB8 : MB mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(clear; lia) G2); exists 512; reflexivity).
assert (MSZ8 : MSZ mod 8 = 0).
{ unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed n + rz_size n + 4095) / 4096) * 512 + 512). clear; lia. }
assert (ESH : shad (MB + MSZ) = shad MB + MSZ / 8) by (apply shad_add8'; assumption).
assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; clear - N5 N6 N4; lia).
eapply evt_cut.
{ unfold mad_eff.
apply (secdealloc_A2_spec (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' (Z_to_bv 64 C) (Z_to_bv 64 INST) a4' a5' a6'
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p) mA MB MSZ (needed n + rz_size n) (Z.of_nat k) PAB 0x4000 (Z.of_nat NS)
(s_mb lst) TCX T lo ws muw mudw); rewrite ?RSP.
all: try assumption.
- split; [exact G2|]. split; [clear - Hbig Hn1; lia|].
unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed n + rz_size n + 4095) / 4096) + 1). clear; lia.
- unfold gobj. clear - G1 G3 G4 G5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - PA1 PA3 PA4 PA5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - Y1 Y3 Y4 Y5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - X1 X3 X4 X5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- clear - LG1 LG3 LG4 LG5 HLk Lbig Ln1. unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold sapart. clear - AP23. lia.
- unfold sapart. clear - AP12. lia.
- unfold sapart. clear - ALT Lbig Ln1. lia.
- clear - Hkl SW1 Hwsl. unfold SEC_MAX in *. lia.
- clear - HSB HLk. destruct HSB as (? & _ & ? & _). unfold kHighShadowEnd in *. lia.
- clear - N5. lia.
- clear - N6. lia. }
intros ms2 P2.
destruct P2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & m2 & -> & MU2 & WM2 & MI2 & UF2 & ST2 & K2).
rewrite RSP in MU2, ST2.
apply evt_done.
set (W0 := qcbrec_sec_W T (C - 112) ++ [(shad MB, shad MB + MSZ / 8); (C - 112 - 96, C - 112); (C - 112 - 32, C - 112);
(i_sec_mutex, i_sec_mutex + 4); (i_sec_nres + 8, i_sec_nres + 16); (i_sec_sorted, i_sec_sorted + 40);
(PAB + 8 * Z.of_nat k, PAB + 8 * Z.of_nat k + 8); (i_gstat_alloc, i_gstat_alloc + 16)] ++ sd_W3 (C - 112) MB MSZ T).
apply (ds_fin W0 lst ws m2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw Hlst Hwsl Hwsf); [| exact (wmono_trans _ _ _ _ WM1 WM2) | | exact K2 | exact MI2 | exact UF2 | exact ST2].
- apply (munch_trans (W0 ++ [(s_mb lst + 24, s_mb lst + 32)]) m mA m2).
+ apply (munch_weaken (qcbrec_sec_W T (C - 112) ++ sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) _ m mA); [|exact MU1]. intros x Hx. refine (outside_incl _ _ x _ Hx).
intros iv Hiv. subst W0. unfold qcbrec_sec_W, sd_W, sd_W1, sd_W3 in *. cbn [app In] in Hiv |- *. clear - Hiv.
repeat (destruct Hiv as [Hiv|Hiv]; [subst iv; repeat (first [left; reflexivity | right]) |]). destruct Hiv.
+ apply (munch_weaken (sd_W3 (C - 112) MB MSZ T) _ mA m2); [|exact MU2]. intros x Hx. refine (outside_incl _ _ x _ Hx).
intros iv Hiv. subst W0. unfold qcbrec_sec_W, sd_W, sd_W1, sd_W3 in *. cbn [app In] in Hiv |- *. clear - Hiv.
repeat (destruct Hiv as [Hiv|Hiv]; [subst iv; repeat (first [left; reflexivity | right]) |]). destruct Hiv.
- unfold W0, qcbrec_sec_W, sd_W3. cbn [app].
repeat apply Forall_cons; try apply Forall_nil.
+ left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; clear; lia].
+ right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; clear; lia].
+ do 9 right. left. cbn. clear - N5; lia.
+ do 8 right. left. exists k, s. split; [left; reflexivity|]. split; [exact Hk|]. cbn [fst snd]. rewrite ESH. clear; lia.
+ do 9 right. left. cbn. clear - N5; lia.
+ do 9 right. left. cbn. clear - N5; lia.
+ left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; clear; lia].
+ left. exists (i_sec_nres + 8, i_sec_nres + 16). split; [right; left; reflexivity | cbn; clear; lia].
+ left. exists (i_sec_sorted, i_sec_sorted + 40). split; [right; right; left; reflexivity | cbn; clear; lia].
+ do 10 right. cbn. clear - Hkl SW1. unfold SEC_MAX in *. lia.
+ left. exists (i_gstat_alloc, i_gstat_alloc + 16). split; [right; right; right; left; reflexivity | cbn; clear; lia].
+
do 8 right. left. exists k, s. split; [left; reflexivity|]. split; [exact Hk|]. cbn [fst snd].
assert (SH0 : 0 <= shad MB) by (unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(clear - G1; lia) ltac:(clear; lia)); lia).
pose proof (pbeg_facts (shad MB) SH0) as (PBF & _).
pose proof (pend_facts (shad (MB + MSZ)) ltac:(rewrite ESH; pose proof (Z.div_pos MSZ 8 ltac:(clear - Hbig Hn1; lia) ltac:(clear; lia)); lia)) as (PEF & _).
clear - PBF PEF; lia.
+ do 9 right. left. cbn. clear - N5; lia.
+ right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; clear; lia].
Qed.

End RunA.
End RL_dsec_runA.
Export RL_dsec_runA.

Module RL_dsec_ret.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18w X18i X18g X196 X187 X16j X161 X13v X16p X16b X14p X14t X13u X14q X133 X13c X13a X138 X135 X13p X13k.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead RL_dsec_defs RL_dsec_runA.

Lemma ds_client_map : forall Σ k s z a, geo_ok Σ -> live_wf Σ -> nth_error (sec Σ) k = Some s -> s_quar s = true ->
l_ACEIL (lay Σ) <= z -> aclient (live Σ) (frames Σ) z a ->
~ (s_mb s <= a < s_mb s + smsz (s_n s)) /\ (z <= a \/ a < l_ACEIL (lay Σ)).
Proof.
intros Σ k s z a HG Hlive Hk Hq Hz Ha.
pose proof (an_map Σ k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & SW5 & _).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & _ & _ & AF & _). unfold apart in AF.
destruct Ha as [Hs|[Hcs|[Hl|[Hf|Hfs]]]].
- split; [clear - Hs Hz M2; lia | left; lia].
- destruct Hcs as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; split; [clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia |
clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia | clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia].
- destruct Hl as (p & n & Hin & Hx). destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(t & Ht & Htq & Htn & Ep)].
+ pose proof (dk_slot_in Σ HG c' i' _ Hc' Hn) as (S1 & S2 & _).
assert (Hfit : rz_size n + n <= ClassSize c' /\ 0 <= n).
{ pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
pose proof (fl_rz_facts n) as (R1 & R2). subst p. unfold p_ubeg in Hx.
split; [clear - Hx S1 S2 G7 M5 Hfit R1 R2; lia | right; clear - Hx S1 S2 G7 G4 Hfit R1 R2; lia].
+ subst p. unfold s_ubeg in Hx. rewrite <- Htn in Hx.
destruct (In_nth_error _ _ Ht) as (jt & Hjt).
pose proof (dk_map Σ HG _ t Hjt) as (T1 & T2 & _ & _ & _ & _ & _ & T8 & T9).
pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
destruct (Nat.eq_dec jt k) as [->|Hne].
* rewrite Hk in Hjt. injection Hjt as <-. rewrite Hq in Htq. discriminate.
* pose proof (T9 k s Hk (fun E => Hne (eq_sym E))) as A. unfold apart in A.
split; [clear - Hx A Tbig Tn1; lia | right; clear - Hx T2 Tbig Tn1; lia].
- destruct Hf as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
split; [clear - Hx Y1 Y2 Y3 AF; lia | right; clear - Hx Y2 Y3 Q3; lia].
- destruct Hfs as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
pose proof (dk_geo Σ HG) as (Z1 & Z2 & _).
pose proof (dk_shad_rng f ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X1. pose proof (dk_shad_rng (f + fs_size k0) ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X2.
split; [clear - Hx X1 X2 M3; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia | right; clear - Hx X2 G1; lia].
Qed.

Section Ret.
Variables (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat)
(s : secst).
Hypothesis HOK : dl_ok p.
Hypothesis HWP : rt_wfP Σk ((b, skipn i ents) :: rest).
Hypothesis HS : dl_sig p Σk.
Hypothesis Hk : nth_error (sec Σk) k = Some s.
Hypothesis Hq : s_quar s = true.
Hypothesis Hib : nth_error (r_st (pr Σk 24)) ib = Some CkBatch.
Hypothesis Eb : b = p_abeg (l_SB (lay Σk)) 24 ib.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation L := (lay Σk).
#[local] Notation SB := (l_SB (lay Σk)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).

Definition mun_eff : SyscallEffect := mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 (s_mb s), Z_to_bv 64 (smsz (s_n s)))] [] [].

Lemma ds_ret : forall ms0, svc_mun p j b ents i rest Σk k s ms0 -> evt bsegs (dl_N p j b ents i rest (recs Σk k)) (nretA ms0 mun_eff).
Proof using HOK HWP HS Hk Hq Hib Eb.
intros ms0 (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & HA' & MI' & UF' & ST' & LM').
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (an_map Σk k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; clear - N5 N6 N4; lia).
pose proof (dg_consts L m' (proj1 HA')) as (_ & MMG' & _).
eapply evt_mono.
{ unfold mun_eff.
apply (uod_B_spec (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' a2' a3' a4' a5' a6'
(Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p) m' (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1057944)
MB MSZ lo); rewrite ?RSP.
- exact M1. - exact M7. - clear - M2 HLk; lia.
- unfold hide, img_hull_lo, img_hull_hi. clear - M4; unfold SEGTOP_A in *; lia.
- exact UF'. - exact MMG'. - exact ST'.
- clear - HLk G1 G8 G4. unfold kHighShadowEnd, K_HIGH_SHADOW_hi, SHB in *. lia.
- clear - N5; lia. - clear - N6; lia. - exact MI'. }
intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m'' & -> & MU & WB & MI'' & ST'' & _).
rewrite RSP in MU, ST''.
pose proof LM' as ((G & WG & HGo) & RP & FR & QR & QB).

assert (CLI : forall a, aclient (live Σ0) (frames Σ0) (C + 32) a -> outside [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a).
{ intros a Ha. rewrite <- Elv, <- Efr in Ha.
destruct (ds_client_map Σk k s (C + 32) a HG Hlive Hk Hq ltac:(clear - HLk N5; lia) Ha) as (X1 & X2).
cbn [outside]. split; [exact X1|]. split; [|exact I]. clear - X2 HLk N5. lia. }
assert (STA : forall a n0, C - 112 <= a -> 0 <= n0 -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a n0).
{ intros a n0 H1 H2. cbn [disjoint_from]. clear - H1 H2 M2 HLk N5. split; [lia | split; [lia | exact I]]. }
assert (SLA : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] (p_abeg SB 24 j') 8192).
{ intros j' Hj'. pose proof (dk_slot_in Σk HG 24 j' _ ltac:(clear; lia) Hj') as (S1 & S2 & _). change (ClassSize 24) with 8192 in S1, S2.
cbn [disjoint_from]. clear - S1 S2 M5 G7 G4 HLk N5. split; [lia | split; [lia | exact I]]. }
exists (Z_to_bv 64 0x47f68), y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m''.
split; [rewrite ret_pc_even; [reflexivity | clear; lia | reflexivity]|].
split.
-
split; [exact (ds_art_nw Σk k s lo (C - 112) HG Hk HLk ltac:(clear - N5; lia) ltac:(clear - N6; lia) Hdep HQB m' m'' HA' MU)|].
split; [exact MI''|]. split; [exact ST''|].
split.
{ exists ((MB, MB + MSZ) :: G). split.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2). apply (WB x); [clear - Ho1; lia | exact (WG x Hx Ho2)].
- apply Forall_cons; [|exact HGo]. cbn [fst snd]. intros a Ha. split.
+ intros Hc. rewrite <- Elv, <- Efr in Hc.
destruct (ds_client_map Σk k s (C + 32) a HG Hlive Hk Hq ltac:(clear - HLk N5; lia) Hc) as (X1 & _). exact (X1 Ha).
+ clear - Ha M2 HLk. lia. }
split; [exact (rt_pres_trans _ _ _ _ m' m'' RP (fun a Ha => MU a (CLI _ Ha)))|].
split.
{ pose proof FR as (FR1 & FR2 & FR3). split; [|split].
- apply (rwc_nw _ m' m'' _ _ FR1 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
- apply (rwc_nw _ m' m'' _ _ FR2 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
- apply (rwc_nw _ m' m'' _ _ FR3 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia. }
apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
apply (proj2 (qcache_rep_iff _ _ _)). split.
+ apply (rwc_nw _ m' m'' _ _ QH MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
+ apply (qchain_nw _ m' m'' _ QC MU). apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (SLA j' Hj').
- apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (B1 & (ws & U & Hl & Hf) & Hn).
apply (proj2 (qbatch_iff _ _ _ _)). split; [|split; [|exact Hn]].
+ apply (rwc_nw _ m' m'' _ _ B1 MU). cbn [cells_size csize Nat.add Z.of_nat]. rewrite Eb.
apply (dsj_sub _ (p_abeg SB 24 ib) 8192); [exact (SLA ib Hib) | clear; lia | clear; lia].
+ exists ws. split; [|split; [exact Hl | exact Hf]]. apply (u64_nw _ m' m'' _ _ U MU). rewrite Hl. rewrite Eb.
apply (dsj_sub _ (p_abeg SB 24 ib) 8192); [exact (SLA ib Hib) | clear; lia | clear; lia].
Qed.

End Ret.
End RL_dsec_ret.
Export RL_dsec_ret.

Module RL_dsec.
Import X12c X0j9 X14x X0r0 X0j1 X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18w X18i X18g X187 X17i X19i X16j X161 X13v X16p X16b X14p X14t X13u X14q X16o X133 X13c X13a X138 X135 X13t X13w X15h X13k.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead RL_dsec_defs RL_dsec_runA RL_dsec_ret.

Lemma ds_FOP_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
forall l l', Permutation l l' -> ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
intros X R Hs l l' H. induction H as [|x l l' Hp IH|x y l|l l' l'' _ IH1 _ IH2]; intros HF.
- constructor.
- inversion HF as [|? ? Hx Hl]; subst. constructor; [|exact (IH Hl)].
apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hx). exact (Permutation_in _ (Permutation_sym Hp) Hz).
- inversion HF as [|? ? Hy Hl]; subst. inversion Hl as [|? ? Hx Hl']; subst.
inversion Hy as [|? ? Hyx Hyl]; subst.
constructor; [constructor; [exact (Hs _ _ Hyx)| exact Hx]|]. constructor; [exact Hyl| exact Hl'].
- exact (IH2 (IH1 HF)).
Qed.

Lemma ds_FOP_app_cross : forall {X} (R : X -> X -> Prop) l1 l2, ForallOrdPairs R (l1 ++ l2) ->
forall x y, In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|q l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
cbn [app] in H. inversion H as [|? ? Hp Hl]; subst. destruct Hx as [<-|Hx].
- apply (proj1 (Forall_forall _ _) Hp). apply in_or_app. right. exact Hy.
- exact (IH l2 Hl x y Hx Hy).
Qed.

Lemma ds_filter_all_true : forall {X} (f : X -> bool) (l : list X), (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
intros X f l. induction l as [|x l IH]; intros H; [reflexivity|]. cbn [List.filter]. rewrite (H x (or_introl eq_refl)).
f_equal. apply IH. intros y Hy. exact (H y (or_intror Hy)).
Qed.

Lemma ds_perm_filter : forall {X} (f : X -> bool) (l l' : list X), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
intros X f l l' H. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2].
- constructor.
- cbn [List.filter]. destruct (f x); [apply perm_skip; exact IH | exact IH].
- cbn [List.filter]. destruct (f x), (f y); try apply perm_swap; apply Permutation_refl.
- exact (Permutation_trans IH1 IH2).
Qed.

Lemma ds_FOP_filter : forall {X} (R : X -> X -> Prop) (f : X -> bool) (l : list X), ForallOrdPairs R l -> ForallOrdPairs R (List.filter f l).
Proof.
intros X R f l H. induction H as [|x l Hx Hl IH]; [constructor|]. cbn [List.filter]. destruct (f x); [|exact IH].
constructor; [|exact IH]. apply Forall_forall. intros y Hy. apply List.filter_In in Hy as [Hy _].
exact (proj1 (Forall_forall _ _) Hx y Hy).
Qed.

Lemma ds_maps0_pos : forall L, layout_ok L -> Forall (fun e => 0 < bv_unsigned (snd e)) (l_maps0 L).
Proof.
intros L HL. unfold layout_ok in HL.
destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & HP) & _).
exact HP.
Qed.

Lemma ds_filter_map : forall {X Y} (f : Y -> bool) (g : X -> Y) (l : list X),
List.filter f (map g l) = map g (List.filter (fun x => f (g x)) l).
Proof. intros X Y f g l. induction l as [|x l IH]; [reflexivity|]. cbn [map List.filter]. destruct (f (g x)); cbn [map]; rewrite IH; reflexivity. Qed.

Lemma ds_lit_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
intros x y Hx Hy E. rewrite <- (unsigned_lit x Hx), <- (unsigned_lit y Hy). rewrite E. reflexivity.
Qed.

Theorem ds_perm : forall Σ k s mo, nth_error (sec Σ) k = Some s -> geo_ok Σ -> ARTM_A Σ mo ->
Permutation (rt_maps (recs Σ k)) (map_remove (rt_maps Σ) (Z_to_bv 64 (s_mb s))).
Proof.
intros Σ k s mo Hk HG HA.
pose proof (ds_maps0_pos _ (proj1 HG)) as HPOS.
pose proof HA as (Hperm & _ & _ & _ & (_ & _ & Hsep0 & _)).
pose proof (ds_FOP_filter iv_apart vpos _ Hsep0) as Hsep.
pose proof (dk_map Σ HG k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & M9).
pose proof (dk_geo Σ HG) as (_ & G2 & _).
pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
pose proof (nth_error_lt _ _ _ Hk) as Hkl.
unfold rt_maps, map_remove. cbn [recs set_sec sec lay]. rewrite filter_app.
assert (E0 : List.filter (fun q => negb (bv_eqb (fst q) (Z_to_bv 64 (s_mb s)))) (l_maps0 (lay Σ)) = l_maps0 (lay Σ)).
{ apply ds_filter_all_true. intros e He. apply negb_true_iff. destruct (bv_eqb (fst e) (Z_to_bv 64 (s_mb s))) eqn:Eb; [|reflexivity].
exfalso. apply bv_eqb_eq in Eb.
assert (HsepR : ForallOrdPairs iv_apart (map secmap (rev (sec Σ)) ++ l_maps0 (lay Σ)))
by exact (ds_FOP_perm iv_apart (fun x y H => ltac:(unfold iv_apart in *; clear - H; lia)) _ _ Hperm Hsep).
pose proof (ds_FOP_app_cross _ _ _ HsepR (secmap s) e ltac:(apply in_map; apply (proj1 (in_rev _ _)); exact (nth_error_In _ _ Hk)) He) as D.
pose proof (proj1 (Forall_forall _ _) HPOS e He) as Pe.
unfold iv_apart, secmap in D. cbn [fst snd] in D. rewrite Eb in D.
rewrite !unsigned_lit in D by (clear - M1 M2 M8 G2; lia). cbv beta in Pe. clear - D Pe M8. lia. }
rewrite E0. apply Permutation_app_tail.
rewrite ds_filter_map. apply Permutation_map.
eapply perm_trans; [apply Permutation_sym, Permutation_rev|]. eapply perm_trans; [|apply ds_perm_filter, Permutation_rev].
eapply perm_trans; [|apply ds_perm_filter, Permutation_sym, (swap_remove_perm k (sec Σ) s Hk)].
cbn [List.filter]. unfold secmap at 1. cbn [fst]. rewrite bv_eqb_refl. cbn [negb].
rewrite ds_filter_all_true; [apply Permutation_refl|].
intros t Ht. apply negb_true_iff. unfold secmap. cbn [fst].
destruct (bv_eqb (Z_to_bv 64 (s_mb t)) (Z_to_bv 64 (s_mb s))) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_eq in Eb.
destruct (swap_remove_other k (sec Σ) t Hkl Ht) as (jt & Hne & Hjt).
pose proof (dk_map Σ HG jt t Hjt) as (T1 & T2 & _ & _ & _ & _ & _ & T8 & _).
pose proof (M9 jt t Hjt Hne) as A.
apply ds_lit_inj in Eb; [|lia | lia]. lia.
Qed.

Lemma ds_smsz_le : forall n, 64512 < n <= 0x8000000 -> smsz n <= 2 ^ 28.
Proof.
intros n Hn. unfold smsz, pg_up, needed, rounded. rewrite (rz_size_big n) by lia. rewrite !Z.max_l by lia.
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
pose proof (Z.div_mod (8 * ((n + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
pose proof (Z.mod_pos_bound (8 * ((n + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma ds_mad_geo : forall Σ k s, geo_ok Σ -> nth_error (sec Σ) k = Some s ->
pbeg (shad (s_mb s)) mod 4096 = 0 /\ pend (shad (s_mb s + smsz (s_n s))) mod 4096 = 0
/\ pbeg (shad (s_mb s)) < pend (shad (s_mb s + smsz (s_n s)))
/\ (K_LOW_SHADOW_lo <= pbeg (shad (s_mb s)) /\ pend (shad (s_mb s + smsz (s_n s))) <= K_LOW_SHADOW_hi
\/ K_HIGH_SHADOW_lo <= pbeg (shad (s_mb s)) /\ pend (shad (s_mb s + smsz (s_n s))) <= K_HIGH_SHADOW_hi)
/\ (forall p : word, pbeg (shad (s_mb s)) <= bv_unsigned p -> bv_unsigned p + 4096 <= pend (shad (s_mb s + smsz (s_n s))) ->
page_allowedb (rtA_allow Σ) p = true).
Proof.
intros Σ k s HG Hk.
pose proof (dk_map Σ HG k s Hk) as (M1 & M2 & M3 & M4 & _ & _ & _ & M8 & _).
pose proof (dk_geo Σ HG) as (_ & G2 & _).
pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _ & SW6).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & GA & _) & _).
pose proof (proj1 (Forall_forall _ _) SW6 s (nth_error_In _ _ Hk)) as HAW.
pose proof (ds_smsz_le (s_n s) ltac:(lia)) as Hsz.
pose proof (smsz_big (s_n s) ltac:(lia)) as Hbig.
assert (MSZ4 : smsz (s_n s) mod 4096 = 0).
{ unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) + 1). lia. }
assert (MB8 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) GA); exists 512; reflexivity).
assert (MSZ8 : smsz (s_n s) mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) MSZ4); exists 512; reflexivity).
assert (ESE : shad (s_mb s + smsz (s_n s)) = shad (s_mb s) + smsz (s_n s) / 8) by (apply shad_add8'; assumption).
set (MB := s_mb s) in *. set (MSZ := smsz (s_n s)) in *.
assert (SH0 : 0 <= shad MB) by (unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(lia) ltac:(lia)); lia).
assert (Q8lo : 8192 <= MSZ / 8) by (apply Z.div_le_lower_bound; lia).
pose proof (pbeg_facts (shad MB) SH0) as (PBR & PBA).
pose proof (pend_facts (shad (MB + MSZ)) ltac:(rewrite ESE; lia)) as (PER & PEA).
rewrite ESE in PER.
split; [exact PBA|]. split; [exact PEA|]. split; [rewrite ESE; lia|].
split.
{ rewrite ESE. clear - M1 M2 M4 G2 PBR PER ESE MB8 MSZ8. unfold shad in *. pose proof (Z.div_mod MB 8 ltac:(lia)) as D1.
pose proof (Z.div_mod (MB + MSZ) 8 ltac:(lia)) as D2. rewrite MB8 in D1. rewrite Z.add_mod, MB8, MSZ8 in D2 by lia. cbn in D2.
unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. destruct M4 as [X|X]; [left | right]; lia. }
intros p' H1 H2. rewrite ESE in H2. unfold page_allowedb. apply existsb_exists. exists (pg_dn (shad MB), pg_up (shad (MB + MSZ))).
split; [unfold rtA_allow; apply in_or_app; left; exact HAW|]. cbn [fst snd]. unfold page_size.
pose proof (pg_dn_facts (shad MB) ltac:(unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(lia) ltac:(lia)); lia)) as (D1 & _).
pose proof (pg_up_facts (shad (MB + MSZ)) ltac:(unfold shad, SHB; pose proof (Z.div_pos (MB + MSZ) 8 ltac:(lia) ltac:(lia)); lia)) as (U1 & _).
apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Section ISec.
Variable p : dlp.
Hypothesis MN : munmap_node.
Hypothesis AN : madvise_node.
Hypothesis HOK : dl_ok p.
#[local] Notation PMc := (dl_PMc p).

Lemma ds_mun : forall j Σk b ib ents i rest k s, rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib -> nth_error (sec Σk) k = Some s -> s_quar s = true ->
cps bsegs (ASTA RTA Σk PMc (svc_mun p j b ents i rest Σk k s)) (ASTA RTA (recs Σk k) PMc (dl_N p j b ents i rest (recs Σk k))).
Proof using MN HOK.
intros j Σk b ib ents i rest k s HWP HS Hib Eb Hk Hq.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & HR & _ & HSW & _ & _ & HB & _).
pose proof HB as (B1 & B2 & B3 & B4 & B5).
pose proof (dk_map Σk HG k s Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof HSW as (_ & _ & _ & SW4 & _). pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & (G1 & G2 & _) & _).
eapply cps_seq.
- intros T cf Hcf HK. pose proof Hcf as (_ & _ & (HAM & _) & _). cbn [ARTM RTA] in HAM.
apply (MN Σk (recs Σk k) PMc (svc_mun p j b ents i rest Σk k s) (fun ms => exists ms0, svc_mun p j b ents i rest Σk k s ms0 /\ ms = nretA ms0 (mun_eff s))
(s_mb s) (smsz (s_n s)) FDO MST eq_refl eq_refl); [| | | exact HL | clear - B1 B3; lia | exact B4 | exact M8 | | clear - M1; lia | exact G2 | exact M2 | | exact Hcf | exact HK].
+ change (In (secmap s) (map secmap (rev (sec Σk)))). apply in_map. apply (proj1 (in_rev _ _)). exact (nth_error_In _ _ Hk).
+ exact (ds_perm Σk k s (cfg_model cf) Hk HG HAM).
+ pose proof (secsum_recs Σk k s Hk) as E. unfold rt_eager. change (secsum Σk) with (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec Σk)) in E.
change (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec (recs Σk k))) with (secsum (recs Σk k)).
change (sum_cls (fun c => r_muser (pr (recs Σk k) c) + r_mfa (pr (recs Σk k) c)) 31) with (sum_cls (fun c => r_muser (pr Σk c) + r_mfa (pr Σk c)) 31).
change (sec_nres (recs Σk k)) with (sec_nres Σk). rewrite E. clear; lia.
+ unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) + 1). clear; lia.
+ intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & _).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists (MSsvc (uod_regs (Z_to_bv 64 0x47f68) (Z_to_bv 64 (dl_usp p - 2288 - 112))
(dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s)) a2' a3' a4' a5' a6' (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37))
(Z_to_bv 64 (Z.of_nat (length ents))) (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16))
(Z_to_bv 64 (16 + Z.of_nat i)) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6') (dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215)
(dl_fc p) None m' (seg_rom bsegs)). split; [exact Hms | reflexivity].
- apply (dl_evt (recs Σk k) PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
exact (ds_ret p j b ib ents i rest Σk k s HOK HWP HS Hk Hq Hib Eb ms0 Hms0).
Qed.

Theorem item_sec_ok : item_sec_stmt p.
Proof using MN AN HOK.
intros j Σk b ib ents i rest k s Hi HWP HS Hib Eb Hk Hq Hent.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
assert (Esk : skipn i ents = (s_mb s + 6128, s_n s) :: skipn (S i) ents)
by (rewrite (skipn_nth_cons ents i (0, 0) Hi), Hent; reflexivity).
assert (HWPc : rt_wfP Σk ((b, (s_mb s + 6128, s_n s) :: skipn (S i) ents) :: rest)) by (rewrite <- Esk; exact HWP).
pose proof (rt_wfP_recs Σk b _ _ (skipn (S i) ents) rest k s HWPc Hk Hq eq_refl eq_refl) as HWP'.
eapply (cps_conseq bsegs); [| intros cf Hcf; exact Hcf |].
2:{ intros cf Hcf. exists (recs Σk k). split; [exact Hcf|]. split; [exact HWP'|].
pose proof (recs_fields Σk k) as (X1 & X2 & _ & X4 & _ & _ & _ & X8 & _ & _ & X11 & X12 & X13).
split; [split; [rewrite X1; exact El|]; split; [rewrite X12; exact Elv|]; split; [rewrite X13; exact Efr|];
split; [rewrite X11; exact Ecr|]; split; [rewrite X8; exact Eql | split; [rewrite X4; exact Einit | exact Epo]]|].
rewrite X2. exact Hib. }
apply cps_pointwise. intros ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
rewrite Hent. cbn [fst].
change (MS (mkR (Z_to_bv 64 0x47f68) (Z_to_bv 64 (dl_usp p - 2288 - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (dl_usp p - 2288))
(Z_to_bv 64 INST) (Z_to_bv 64 (dl_usp p - 2288 - 104)) (Z_to_bv 64 (s_mb s + 6128)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom bsegs))
with (ds_ms p b ents i s m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).

apply (cps_seq bsegs _ (ASTA RTA Σk PMc (svc_mad p b ents i Σk k s m))).
{ apply (dl_evt Σk PMc _ _ MST). intros ms0 <-.
exact (ds_run1 p j b ib ents i rest Σk k s m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HOK HWP HS Hk Hq DM QB Hib Eb). }
apply (cps_seq bsegs _ (ASTA RTA Σk PMc (fun ms => exists ms0, svc_mad p b ents i Σk k s m ms0 /\ ms = nretA ms0 (mad_eff s)))).
2:{ apply (cps_seq bsegs _ (ASTA RTA Σk PMc (svc_mun p j b ents i rest Σk k s))).
- apply (dl_evt Σk PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
exact (ds_run2 p j b ib ents i rest Σk k s m HOK HWP HS Hk Hq DM QB Hib Eb ms0 Hms0).
- exact (ds_mun j Σk b ib ents i rest k s HWP HS Hib Eb Hk Hq). }

pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & _).
pose proof (ds_mad_geo Σk k s HG Hk) as (R1 & R2 & R3 & R5 & R6).
apply (AN Σk PMc (svc_mad p b ents i Σk k s m) (fun ms => exists ms0, svc_mad p b ents i Σk k s m ms0 /\ ms = nretA ms0 (mad_eff s))
(pbeg (shad (s_mb s))) (pend (shad (s_mb s + smsz (s_n s)))) FDO MST HL R1 R2 R3 R5 R6).
intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & mA & ws & lst & muw & mudw & -> & _).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
eexists. split; [exact Hms | reflexivity].
Qed.

End ISec.
End RL_dsec.
Export RL_dsec.

Module RL_drain_fin.
Import X12c X0j9 X14x X0r0 X0j1 X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18s X18w X18i X18g X174 X16j X161 X13v X16p X16b X14p X14t X13u X14q X140 X16o X133 X13c X13a X13g X138 X135 X12w X14r.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead RL_dsec_defs RL_dsec_runA RL_dsec_ret RL_dsec.

Definition dr_post (F : bvmap 5 word) (fc : bv 32) (Σ : rtsA) (PMc : Model -> Prop) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (m : mem) :
config -> Prop :=
fun cf => exists Σ' : rtsA,
ASTA RTA Σ' PMc (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x46800) fc None m' (seg_rom bsegs)
/\ ART_A Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -2128)
/\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m') cf
/\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ rtA_pois Σ' = rtA_pois Σ.

Lemma rw_cells_agree_nw : forall (m m' : mem) A cs, rw_cells bsegs m A cs ->
(forall a : word, A <= bv_unsigned a < A + Z.of_nat (cells_size cs) -> m' a = m a) -> rw_cells bsegs m' A cs.
Proof.
intros m m' A cs ((Hwf & (B0 & B1 & Hb)) & (W0 & W1 & Hw)) Hag.
pose proof (cells_bytes_length cs Hwf) as Hl.
split; [split; [exact Hwf|]|].
- split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite (Hag (wa (A + Z.of_nat i))); [exact (Hb i Hi)|].
rewrite wa_unsigned by lia. lia.
- split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hw i Hi) as X. unfold wview in X |- *.
rewrite (Hag (wa (A + i))); [exact X|]. rewrite wa_unsigned by lia. lia.
Qed.

Section DFin.
Variable p : dlp.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

Theorem rec_from_R : forall (Σ' : rtsA) (m0 : mem) (s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 : word),
qrec_frame (dl_m0 p) C (Z_to_bv 64 0x4a16c) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4 ->
qput_frame (dl_m0 p) (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6 ->
rt_pres (live Σ0) (frames Σ0) (usp + -2128) m0 (dl_m0 p) -> rt_wfP Σ' [] -> dl_sig p Σ' ->
cps bsegs (ASTA RTA Σ' PMc (dl_R p Σ'))
(dr_post (dl_F p) (dl_fc p) Σ0 PMc (dl_gp p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) w0 w1 w2 w3 w4 w5 s6 lo usp m0).
Proof using HOK.
intros Σ' m0 s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 QF PF RP0 HWP HS.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
assert (HL : l_ACEIL (lay Σ') <= lo) by (rewrite El; exact N9).
assert (Esp1 : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
assert (Esp2 : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
apply cps_pointwise.
intros ms (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & MI & ST & (G & WG & HGo) & RP & QR).

assert (QF1 : qrec_frame m (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80) (Z_to_bv 64 0x4a16c) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4).
{ rewrite Esp1. replace (usp + -2208 + -80) with (usp - 2288) by lia. unfold qrec_frame in *.
apply (rw_cells_agree_nw (dl_m0 p) m _ _ QF). intros a Ha. apply RP. left. cbn [cells_size csize Nat.add Z.of_nat] in Ha. unfold USTACK_TOP. lia. }
assert (PF1 : qput_frame m (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6).
{ unfold qput_frame in *. apply (rw_cells_agree_nw (dl_m0 p) m _ _ PF). intros a Ha. apply RP. left.
cbn [cells_size csize Nat.add Z.of_nat] in Ha. unfold USTACK_TOP. lia. }
destruct QR as (QH & _).
replace (usp - 2288) with (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80) in QH, ST by (rewrite Esp1; lia).
eapply (cps_seq bsegs).
{ eapply (dl_evt Σ' PMc _ _ MST). intros ms0 <-.
rewrite (ret_pc_even 0x47cac); [|lia|reflexivity].
replace (Z_to_bv 64 (usp - 2288)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80)) by (rewrite Esp1; f_equal; lia).
eapply evt_mono; [eapply (qrec_ret_spec (Z_to_bv 64 0x4a16c) (Z_to_bv 64 (usp + -2208)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p)
a0 a1 a2 a3 a4 a5 a6 a7 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (Z_to_bv 64 0x47cac) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4
_ _ _ _ (dl_F p) (dl_fc p) m lo)|].
1: exact QH. 1: exact QF1. 1: exact ST. 1: rewrite Esp1; lia. 1: exact N4. 1: exact MI.
intros ms' P. exact (conj P (conj A (conj MI (conj RP PF1)))). }
apply cps_pointwise.
intros ms ((t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1) & A0 & MI0 & RP0' & PF0).
rewrite Esp1 in MU1, ST1.
assert (HW1 : Forall (fun iv => lo <= fst iv /\ snd iv <= usp + -2128) [(usp + -2208 - 80, usp + -2208)]) by (repeat constructor; cbn [fst snd]; lia).
pose proof (artc_stk Σ' m m1 _ lo (usp + -2128) HG HL HW1 A Hdep HQB MU1 WM1) as A1.
pose proof (client_stk Σ' m m1 _ lo (usp + -2128) HG HL ltac:(lia) HW1 Hlive MU1) as RP1. rewrite Elv, Efr in RP1.
assert (PF2 : qput_frame m1 (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6).
{ rewrite Esp2. replace (usp + -2128 - 80) with (usp + -2208) by lia. unfold qput_frame in *.
apply (rw_cells_transport bsegs _ m m1 _ _ PF0 MU1 WM1). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. lia. }
assert (ST1' : stk bsegs m1 lo (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80)) by (rewrite Esp2; replace (usp + -2128 - 80) with (usp + -2208) by lia; exact ST1).
eapply (cps_seq bsegs).
{ eapply (dl_evt Σ' PMc _ _ MST). intros ms0 <-.
rewrite (ret_pc_even 0x4a16c); [|lia|reflexivity].
replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80)) by (rewrite Esp2; f_equal; lia).
eapply evt_mono; [apply (qput_C_spec (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 (dl_r5 p) (dl_r6 p)
(dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (Z_to_bv 64 0x4a16c)
w0 w1 w2 w3 w4 w5 s6 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (dl_F p) (dl_fc p) m1 lo)|].
1: exact PF2. 1: exact ST1'. 1: rewrite Esp2; lia. 1: exact N4. 1: exact MI1.
intros ms' P. exact (conj P (conj A1 (conj RP0' RP1))). }
intros T0 cf Hcf Hk. apply Hk. exists Σ'.
split; [| split; [exact Elv | split; [exact Efr | split; [exact El | exact (conj Ecr (rtA_pois_eq _ _ Efr Epo))]]]].
unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms ((t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2)
& A1' & RP0'' & RP1').
rewrite Esp2 in MU2, ST2.
rewrite (ret_pc_even 0x46800); [|lia|reflexivity].
exists t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
assert (HW2 : Forall (fun iv => lo <= fst iv /\ snd iv <= usp + -2128) [(usp + -2128 - 80, usp + -2128)]) by (repeat constructor; cbn [fst snd]; lia).
pose proof (artc_stk Σ' m1 m2 _ lo (usp + -2128) HG HL HW2 A1' Hdep HQB MU2 WM2) as A2.
pose proof (client_stk Σ' m1 m2 _ lo (usp + -2128) HG HL ltac:(lia) HW2 Hlive MU2) as RP2. rewrite Elv, Efr in RP2.
split; [exact (c_ART Σ' m2 (rt_wfP_nil Σ' HWP) A2)|]. split; [exact MI2|]. split; [exact ST2|].
refine (rt_pres_trans _ _ _ _ m1 m2 _ RP2). refine (rt_pres_trans _ _ _ _ m m1 _ RP1').
refine (rt_pres_trans _ _ _ _ (dl_m0 p) m RP0 _). exact (rt_pres_mono _ _ (C + 32) (usp + -2128) _ _ RP ltac:(lia)).
Qed.

End DFin.

Theorem item_ok : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt p) -> forall p, dl_ok p -> item_stmt p.
Proof.
intros FC ISEC p HOK j Σk b ib ents i rest Hi HWP HS Hib Eb.
assert (Hq : qent_ok Σk (nth i ents (0, 0))).
{ pose proof HWP as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & Q7 & _) & _). unfold qentsP, qallP in Q7.
apply (proj1 (Forall_forall _ _) Q7). apply in_flat_map. exists (b, skipn i ents).
split; [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity|].
cbn [snd]. rewrite (skipn_nth_cons ents i (0, 0) Hi). left. reflexivity. }
destruct Hq as [(c & ic & Hc & Hic & Eh)|(s & Hs & Hsq & Hn & Eh)].
- apply (item_prim_ok p FC HOK j Σk b ib ents i rest c ic (snd (nth i ents (0, 0))) Hi HWP HS Hib Eb Hc Hic).
rewrite <- Eh. destruct (nth i ents (0, 0)); reflexivity.
- destruct (In_nth_error _ _ Hs) as (k & Hk).
apply (ISEC p HOK j Σk b ib ents i rest k s Hi HWP HS Hib Eb Hk Hsq). rewrite <- Eh, Hn. destruct (nth i ents (0, 0)); reflexivity.
Qed.

Lemma dd_switch : forall (Σ Σ' : rtsA) (PMc : Model -> Prop) (P : machine_state -> Prop), lay Σ' = lay Σ -> sec Σ' = sec Σ ->
rt_eager Σ' = rt_eager Σ -> aw Σ' = aw Σ -> cps bsegs (ASTA RTA Σ PMc P) (ASTA RTA Σ' PMc P).
Proof.
intros Σ Σ' PMc P El Es Ee Ea T cf Hcf Hk. apply Hk. unfold ASTA in *. cbn [rt_allow ARTM RTA] in *.
replace (rtA_allow Σ') with (rtA_allow Σ) by (unfold rtA_allow; rewrite El, Ea; reflexivity).
eapply AST_conseq; [exact Hcf | intros ms X; exact X |]. intros mo (HM & HP). split; [|exact HP]. exact (artm_eq Σ Σ' mo El Es Ee HM).
Qed.

Theorem drain_rec : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt p) ->
forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
fdfs_only PMc -> mat_stable PMc ->
ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < X16j.qbytes (ql Σ) ->
qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6 ->
stk bsegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
mem_inv bsegs m ->
0x10000000 < X18y.qbytes (qg Σ ++ ql Σ) ->
cps bsegs (ASTA RTA Σ PMc (eq (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
(dr_post F fc Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
intros FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr.
pose proof (xr_geo Σ HW) as (HG & _).
pose proof (rt_wfP_start Σ HW HC) as HWP1.
eapply (cps_seq bsegs).
{ eapply (dl_evt Σ PMc _ _ MST). intros ms <-.
exact (rr_evt Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr). }
eapply (cps_seq bsegs); [exact (dd_switch Σ (set_q Σ [] (rec_r (qg Σ ++ ql Σ) QMIN)) PMc _ eq_refl eq_refl eq_refl eq_refl)|].
apply cps_pointwise.
intros ms (t0' & t1' & t2' & s0' & s1' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & t3' & t4' & t5' & t6' & m3 & -> & A3 & QR3 & QF3 & PF3
& ST3 & MI3 & WM3 & RP3).
pose (p := mkDLP Σ m3 usp lo PMc gp s10 s11 F fc s0' s1' s2' s3' s4' s5 (Z_to_bv 64 0x100000) s7 s8 s9).
assert (HOK : dl_ok p) by (split; [exact FDO|]; split; [exact MST|]; split; [exact HLO|]; split; [exact HLO2|]; split; [exact HSP | exact HG]).
assert (Einit : ca_init Σ = true).
{ destruct (ca_init Σ) eqn:E; [reflexivity|]. exfalso.
pose proof HW as (_ & HR & _ & _ & (_ & _ & Q4 & _) & _). pose proof (proj2 (proj2 (proj2 (proj2 (proj2 HR)))) E 24) as E24.
destruct (qg Σ ++ ql Σ) as [|b0 bs] eqn:EG.
- cbn in HBYr. lia.
- assert (Hb0 : In b0 (ql Σ ++ qg Σ)) by (apply (Permutation_in _ (Permutation_app_comm (qg Σ) (ql Σ))); rewrite EG; left; reflexivity).
destruct (proj1 (Forall_forall _ _) Q4 b0 Hb0) as (ib & Hib & _). rewrite E24 in Hib. destruct ib; discriminate. }
assert (HS1 : dl_sig p (set_q Σ [] (rec_r (qg Σ ++ ql Σ) QMIN))) by (repeat split; [exact Einit]).
pose proof (item_ok FC ISEC p HOK) as ITEM. pose proof (batch_ok p FC HOK) as BATCH.
eapply (cps_seq bsegs).
{ eapply (cps_conseq bsegs); [exact (dl_from_E p HOK ITEM BATCH _ (rec_x (qg Σ ++ ql Σ) QMIN) HWP1 HS1) | | intros cf Hcf; exact Hcf].
intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms E. rewrite <- E. exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6', m3. split; [reflexivity|].
split; [exact A3|]. split; [exact QR3|]. split; [exact ST3|]. split; [exact MI3|].
split; [exists []; split; [exact (wmono_out_nil m3 m3 (wmono_refl bsegs m3)) | constructor]|].
intros a _. reflexivity. }
apply dl_cps_ex. intros Σ' (HWP' & HS').
exact (rec_from_R p HOK Σ' m s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 QF3 PF3 RP3 HWP' HS').
Qed.

Theorem drain_ok : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt p) ->
forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
fdfs_only PMc -> mat_stable PMc ->
ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < X16j.qbytes (ql Σ) ->
qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) w0 w1 w2 w3 w4 w5 s6 ->
stk bsegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
mem_inv bsegs m ->
cps bsegs (ASTA RTA Σ PMc (eq (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
(dr_post F fc Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
intros FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI.
destruct (Z_le_gt_dec (X18y.qbytes (qg Σ ++ ql Σ)) 0x10000000) as [Hx|Hr].
- eapply (cps_conseq bsegs);
[exact (drain_xfer Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
w0 w1 w2 w3 w4 w5 s6 FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI Hx) | intros cf X; exact X |].
intros cf (Σ' & Hcf & E1 & E2 & E3 & E4). exists Σ'. split; [|exact (conj E1 (conj E2 (conj E3 E4)))].
unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & X1 & X2 & _ & X4 & X5).
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [reflexivity | exact (conj X1 (conj X2 (conj X4 X5)))].
- exact (drain_rec FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
w0 w1 w2 w3 w4 w5 s6 FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI ltac:(lia)).
Qed.
End RL_drain_fin.
Export RL_drain_fin.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Module RL_stmt.
Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0gp X0h2 X0j3 X0i7 X0fy X0fg X0e5.

Definition drain_stmt : Prop :=
forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
fdfs_only PMc -> mat_stable PMc ->
ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < qbytes (ql Σ) ->
qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6 ->
stk asegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
mem_inv asegs m ->
cps asegs
(ASTA RTA Σ PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4a148) fc None m (seg_rom asegs))))
(fun cf => exists Σ' : rtsA,
ASTA RTA Σ' PMc (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x46714) fc None m' (seg_rom asegs)
/\ ART_A Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2128)
/\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m') cf
/\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ rtA_pois Σ' = rtA_pois Σ).
End RL_stmt.
Export RL_stmt.

Module RL_drain_ldefs.
Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0j3 X0gp X0id X0i8 X0ib X0hx X0hv X0gj X0fy X0fg X0e5 X0ci X0cp X0cv.
Import RL_stmt.

Record dlp : Type := mkDLP {
dl_Σ0 : rtsA; dl_m0 : mem; dl_usp : Z; dl_lo : Z; dl_PMc : Model -> Prop;
dl_gp : word; dl_s10 : word; dl_s11 : word; dl_F : bvmap 5 word; dl_fc : bv 32;
dl_r0 : word; dl_r1 : word; dl_r2 : word; dl_r3 : word; dl_r4 : word; dl_r5 : word; dl_r6 : word; dl_r7 : word; dl_r8 : word;
dl_r9 : word }.

Definition wmono_out (G : list ivl) (m m' : mem) : Prop :=
forall x : word, wview asegs m x <> None -> outside G (bv_unsigned x) -> wview asegs m' x <> None.

Lemma wmono_out_nil : forall (m m' : mem), wmono asegs m m' -> wmono_out [] m m'.
Proof. intros m m' H x Hx _. exact (H x Hx). Qed.
Lemma wmono_out_wmono : forall G (m1 m2 m3 : mem), wmono_out G m1 m2 -> wmono asegs m2 m3 -> wmono_out G m1 m3.
Proof. intros G m1 m2 m3 H1 H2 x Hx Ho. exact (H2 x (H1 x Hx Ho)). Qed.
Lemma dl_outside_app : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof.
induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn [app outside] in *; [split; [exact I | exact H]|].
destruct H as (H1 & H2). destruct (IH W2 x H2) as (A & B). split; [split; [exact H1 | exact A] | exact B].
Qed.
Lemma wmono_out_trans : forall G1 G2 (m1 m2 m3 : mem), wmono_out G1 m1 m2 -> wmono_out G2 m2 m3 -> wmono_out (G2 ++ G1) m1 m3.
Proof.
intros G1 G2 m1 m2 m3 H1 H2 x Hx Ho. pose proof (dl_outside_app G2 G1 _ Ho) as (O2 & O1). exact (H2 x (H1 x Hx O1) O2).
Qed.

Section Vocab.
Variable p : dlp.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).

Definition dl_gone (G : list ivl) : Prop :=
Forall (fun r => forall a, fst r <= a < snd r -> ~ aclient (live Σ0) (frames Σ0) (C + 32) a /\ ~ (dl_lo p <= a < C + 32)) G.

Definition dl_mem (j : list byte) (Σk : rtsA) (rest : list batch) (m : mem) : Prop :=
ARTc Σk m /\ mem_inv asegs m /\ stk asegs m (dl_lo p) (C - 112) /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone G)
/\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
/\ drec_frame m C j (T + 208) (usp - 2056) (Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
/\ qcache_rep m C rest.

Definition dl_sig (Σk : rtsA) : Prop :=
lay Σk = lay Σ0 /\ live Σk = live Σ0 /\ frames Σk = frames Σ0 /\ credit Σk = credit Σ0 /\ ql Σk = [] /\ ca_init Σk = true /\ pois Σk = pois Σ0.

Definition dl_Q (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
(Z_to_bv 64 (C - 104)) (Z_to_bv 64 (fst (nth i ents (0%Z, 0%Z)))) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom asegs)
/\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

Definition dl_N (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 0x47e7c) (dl_fc p) None m (seg_rom asegs)
/\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

Definition dl_D (j : list byte) (b : Z) (ents : list (Z * Z)) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR (Z_to_bv 64 0x47eb4) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
(Z_to_bv 64 (T + 208)) (Z_to_bv 64 INST) (Z_to_bv 64 24) (Z_to_bv 64 b) a4 a5 a6 a7
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) s6 s7 s8 s9
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 cdealloc_entry) (dl_fc p) None m (seg_rom asegs)
/\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

Definition dl_B (j : list byte) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) s4 (Z_to_bv 64 (2^37)) s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 0x47eb4) (dl_fc p) None m (seg_rom asegs)
/\ dl_mem j Σk rest m.

Definition dl_R (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR (Z_to_bv 64 0x47bc0) (Z_to_bv 64 C) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a0 a1 a2 a3 a4 a5 a6 a7
(dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (ret_pc (Z_to_bv 64 0x47bc0)) (dl_fc p) None m (seg_rom asegs)
/\ ARTc Σk m /\ mem_inv asegs m /\ stk asegs m (dl_lo p) C /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone G)
/\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m /\ qcache_rep m C [].

Definition dl_fin : config -> Prop :=
fun cf => exists Σ' : rtsA, ASTA RTA Σ' (dl_PMc p) (dl_R Σ') cf /\ rt_wfP Σ' [] /\ dl_sig Σ'.

End Vocab.

Definition dl_av (Σ : rtsA) (zhi : Z) (W : list ivl) : Prop :=
(forall ib a n, nth_error (r_st (pr Σ 24)) ib = Some CkBatch -> p_abeg (l_SB (lay Σ)) 24 ib <= a ->
a + n <= p_abeg (l_SB (lay Σ)) 24 ib + 8192 -> disjoint_from W a n)
/\ (forall a n, zhi <= a -> a + n <= USTACK_TOP -> disjoint_from W a n).

Lemma qwf_of_wfP : forall Σ P, rt_wfP Σ P -> qwf (l_SB (lay Σ)) P.
Proof.
intros Σ P (H1 & HR & HV & HS & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & _).
unfold qallP in Q4, Q5, Q6. unfold qentsP, qallP in Q7.
split.
{ apply NoDup_ListNoDup in Q5. rewrite !map_app in Q5. apply NoDup_app_remove_l in Q5. apply NoDup_app_remove_l in Q5. exact Q5. }
apply Forall_forall. intros b Hb.
assert (Hb' : In b (ql Σ ++ qg Σ ++ P)) by (apply in_app_iff; right; apply in_app_iff; right; exact Hb).
destruct (proj1 (Forall_forall _ _) Q4 b Hb') as (i & Hi & Eb). pose proof (proj1 (Forall_forall _ _) Q6 b Hb') as Hl.
pose proof HR as (HR1 & _). pose proof (HR1 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W11).
pose proof H1 as (_ & _ & _ & _ & _ & HSB & _). change (ClassSize 24) with 8192 in W11.
assert (Hlt : (i < length (r_st (pr Σ 24)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
unfold p_abeg in Eb. change (ClassSize 24) with 8192 in Eb. unfold r24.
split; [rewrite Eb; apply Z.mod_divide; [lia|]; apply Z.mod_divide in HSB; [|lia]; destruct HSB as (q & Hq);
exists (q * 8 + 24 * 2 ^ 19 + Z.of_nat i); lia|].
split; [lia|]. split; [lia|]. split; [exact Hl|].
apply Forall_forall. intros e He.
assert (Hq : In e (flat_map snd (ql Σ ++ qg Σ ++ P))) by (apply in_flat_map; exists b; split; [exact Hb' | exact He]).
pose proof (qent_n_pos Σ e HR HS (proj1 (Forall_forall _ _) Q7 e Hq)). lia.
Qed.
End RL_drain_ldefs.
Export RL_drain_ldefs.

Module RL_drain_istmt.
Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0j3 X0gp X0id X0hx X0hv X0fy X0fg X0e5 X0e8 X0ci.
Import RL_stmt RL_drain_ldefs.

Definition dl_ok (p : dlp) : Prop :=
fdfs_only (dl_PMc p) /\ mat_stable (dl_PMc p) /\ l_ACEIL (lay (dl_Σ0 p)) <= dl_lo p /\ dl_lo p + 0x4000 <= dl_usp p + -2208
/\ dl_usp p <= 2 ^ 47 /\ geo_ok (dl_Σ0 p).

Definition item_post (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) : config -> Prop :=
fun cf => exists Σk' : rtsA, ASTA RTA Σk' (dl_PMc p) (dl_N p j b ents i rest Σk') cf
/\ (rt_wfP Σk' ((b, skipn (S i) ents) :: rest) /\ dl_sig p Σk' /\ nth_error (r_st (pr Σk' 24)) ib = Some CkBatch).

Definition item_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps asegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition item_prim_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (c : Z) (ic : nat) (n : Z),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
1 <= c <= 31 -> nth_error (r_st (pr Σk c)) ic = Some (CkQuar n) ->
nth i ents (0, 0) = (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16, n) ->
cps asegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition item_sec_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (k : nat) (s : secst),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
nth_error (sec Σk) k = Some s -> s_quar s = true -> nth i ents (0, 0) = (s_mb s + 6128, s_n s) ->
cps asegs (ASTA RTA Σk (dl_PMc p) (dl_Q p j b ents i rest Σk)) (item_post p j b ib ents i rest).

Definition batch_stmt (p : dlp) : Prop :=
forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (rest : list batch),
rt_wfP Σk ((b, []) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps asegs (ASTA RTA Σk (dl_PMc p) (dl_D p j b ents rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' (dl_PMc p) (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).
End RL_drain_istmt.
Export RL_drain_istmt.

Module RL_drain_loop.
Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb X0hi X0hs X0j3 X0gp X0id X0i8 X0ib X0hx X0hv X0fy X0fg X0da X0e4 X0e8 X0d9 X0e5 X0ci X0cp X0cv X0cn X0ck X0cb.
Import RL_stmt RL_drain_ldefs RL_drain_istmt.

Lemma dl_cps_ex : forall (P : rtsA -> config -> Prop) (phi : rtsA -> Prop) (Q : config -> Prop),
(forall x, phi x -> cps asegs (P x) Q) -> cps asegs (fun cf => exists x, P x cf /\ phi x) Q.
Proof. intros P phi Q H T cf (x & HP & Hphi) Hk. exact (H x Hphi T cf HP Hk). Qed.

Lemma dl_evt : forall (Σk : rtsA) (PMc : Model -> Prop) (Pm Q : machine_state -> Prop), mat_stable PMc ->
(forall ms, Pm ms -> evt asegs Q ms) -> cps asegs (ASTA RTA Σk PMc Pm) (ASTA RTA Σk PMc Q).
Proof. intros Σk PMc Pm Q MST H. exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σk) _ _ _ (fl_ASTA_mat_stable Σk PMc MST) H). Qed.

Lemma geo_of_wfP : forall Σ P, rt_wfP Σ P -> geo_ok Σ.
Proof. intros Σ P (H1 & H2 & _ & H4 & _ & H6 & _). exact (conj H1 (conj H2 (conj H4 H6))). Qed.

Lemma hqb_of_wfP : forall Σ P, rt_wfP Σ P ->
Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Proof.
intros Σ P (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _). unfold qallP in Q4. rewrite app_assoc in Q4. apply Forall_app in Q4. exact (proj1 Q4).
Qed.

Section DLoop.
Variable p : dlp.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).
#[local] Notation FIN := (dl_fin p).
Hypothesis MST : mat_stable (dl_PMc p).
Hypothesis HLO : l_ACEIL (lay (dl_Σ0 p)) <= dl_lo p.
Hypothesis HLO2 : dl_lo p + 0x4000 <= dl_usp p + -2208.
Hypothesis HSP : dl_usp p <= 2 ^ 47.
Hypothesis HG0 : geo_ok (dl_Σ0 p).

Hypothesis ITEM : forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch),
(i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps asegs (ASTA RTA Σk PMc (dl_Q p j b ents i rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_N p j b ents i rest Σk') cf
/\ (rt_wfP Σk' ((b, skipn (S i) ents) :: rest) /\ dl_sig p Σk' /\ nth_error (r_st (pr Σk' 24)) ib = Some CkBatch)).
Hypothesis BATCH : forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (rest : list batch),
rt_wfP Σk ((b, []) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps asegs (ASTA RTA Σk PMc (dl_D p j b ents rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).

Lemma dl_nums : 0 < SB /\ SB_ok (l_ACEIL (lay Σ0)) SB /\ r24 SB + 2 ^ 32 <= lo /\ 0x652000 <= lo /\ lo + 0x400 <= C - 112
/\ C + 32 <= 2 ^ 47 /\ 0 <= T + 208 < 2 ^ 64 /\ 0 <= usp - 2056 < 2 ^ 64 /\ l_ACEIL (lay Σ0) <= lo.
Proof using HLO HLO2 HSP HG0.
pose proof (dk_geo Σ0 HG0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (g_prb Σ0 HG0) as (P1 & P2 & P3).
pose proof (g_grant Σ0 HG0 T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (T1 & T2 & T3 & T4 & T5).
assert (HSB : SB_ok (l_ACEIL (lay Σ0)) SB).
{ pose proof (dg_ok Σ0 HG0) as (_ & X & _). exact X. }
pose proof HSB as (S1 & S2 & S3 & S4). unfold r24, kHighShadowEnd, SEGTOP_A in *.
repeat split; try assumption; lia.
Qed.

Lemma dl_bslot : forall Σk ib, geo_ok Σk -> lay Σk = lay Σ0 -> nth_error (r_st (pr Σk 24)) ib = Some CkBatch ->
0 < p_abeg SB 24 ib /\ p_abeg SB 24 ib + 8192 <= lo /\ r24 SB <= p_abeg SB 24 ib /\ p_abeg SB 24 ib + 8192 <= r24 SB + 2 ^ 32.
Proof using HLO HLO2 HSP HG0.
intros Σk ib HG El Hib. pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof (dk_slot_in Σk HG 24 ib _ ltac:(lia) Hib) as (S1 & S2 & S3 & S4 & S5 & S6). rewrite El in *.
change (ClassSize 24) with 8192 in *. unfold rb, r24, kUserCap in *. repeat split; lia.
Qed.

Lemma dl_mem_step : forall j Σk rest rest' (m m' : mem) (W : list ivl), dl_mem p j Σk rest m -> geo_ok Σk -> dl_sig p Σk ->
live_wf Σk -> depot_ok (dep Σk) (l_DNB (lay Σk)) (l_SSB (lay Σk)) (l_ACEIL (lay Σk)) ->
Forall (fun b => exists j, nth_error (r_st (pr Σk 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σk)) 24 j) (ql Σk ++ qg Σk) ->
Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) W -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (C - 112) ->
drec_mem m' C SB j (T + 208) (usp - 2056) (Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest' ->
dl_mem p j Σk rest' m'.
Proof using HLO HLO2 HSP HG0.
intros j Σk rest rest' m m' W (A & MI & ST & WM0 & RP & FR & QR) HG (El & Elv & Efr & _) Hlive Hdep HQB HW MU WM MI' ST' (FR' & _ & QR').
pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
split; [exact (artc_stk Σk m m' W lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
split; [exact MI'|]. split; [exact ST'|]. split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
split; [|split; [exact FR' | exact QR']].
pose proof (client_stk Σk m m' W lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
intros a Ha. rewrite (RP' a Ha). exact (RP a Ha).
Qed.

Lemma dl_drec : forall j Σk rest (m : mem), dl_mem p j Σk rest m -> lay Σk = lay Σ0 ->
drec_mem m C SB j (T + 208) (usp - 2056) (Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest.
Proof.
intros j Σk rest m (A & _ & _ & _ & _ & FR & QR) El. split; [exact FR|]. split; [|exact QR].
pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
exact (proj1 IC1).
Qed.

Lemma dl_batch_of : forall Σk b ents rest, rt_wfP Σk ((b, ents) :: rest) ->
exists ib, nth_error (r_st (pr Σk 24)) ib = Some CkBatch /\ b = p_abeg (l_SB (lay Σk)) 24 ib.
Proof.
intros Σk b ents rest (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _). unfold qallP in Q4.
assert (Hb : In (b, ents) (ql Σk ++ qg Σk ++ (b, ents) :: rest)) by (apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
destruct (proj1 (Forall_forall _ _) Q4 _ Hb) as (ib & Hib & Eb). exists ib. split; [exact Hib | exact Eb].
Qed.

Lemma dl_from_N : forall k j Σk b ib ents i rest, length ents = (S i + k)%nat ->
rt_wfP Σk ((b, skipn (S i) ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps asegs (ASTA RTA Σk PMc (dl_N p j b ents i rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
induction k as [|k IH]; intros j Σk b ib ents i rest Hlen HWP HS Hib Eb.
-
assert (Hsk : skipn (S i) ents = []) by (apply skipn_all2; lia).
rewrite Hsk in HWP.
eapply (cps_seq asegs); [|exact (BATCH j Σk b ib ents rest HWP HS Hib Eb)].
apply (dl_evt Σk PMc _ _ MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HS as (El & _).
pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4). rewrite El in Eb. subst b.
pose proof DM as (_ & MI & ST & _).
eapply evt_mono; [apply (drec_next_deal_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (usp - 2056) j
(Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
(dl_r8 p) (dl_r9 p) _ ents rest i)|].
1: lia. 1: exact B3. 1: exact B4. 1: exact N2. 1: lia. 1: exact (dl_drec j Σk rest m DM El). 1: exact QB. 1: exact ST. 1: exact N3.
1: lia. 1: lia. 1: exact MI.
intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
exact (dl_mem_step j Σk rest rest m m' [] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP) (Forall_nil _) MU WM MI' ST' DM').
-
pose proof HS as (El & _).
eapply (cps_seq asegs); [| eapply (cps_seq asegs); [exact (ITEM j Σk b ib ents (S i) rest ltac:(lia) HWP HS Hib Eb)|]].
+ apply (dl_evt Σk PMc _ _ MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4). rewrite El in Eb. subst b.
pose proof DM as (_ & MI & ST & _).
eapply evt_mono; [apply (drec_next_qcb_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2056) j
(Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
(dl_r8 p) (dl_r9 p) _ ents rest i)|].
1: lia. 1: exact B1. 1: exact B2. 1: exact (dl_drec j Σk rest m DM El). 1: exact QB. 1: exact ST. 1: lia. 1: lia. 1: exact MI.
intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
exact (dl_mem_step j Σk rest rest m m' [] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP) (Forall_nil _) MU WM MI' ST' DM').
+ apply dl_cps_ex. intros Σk' (HWP' & HS' & Hib').
pose proof HS' as (El' & _).
exact (IH j Σk' b ib ents (S i) rest ltac:(lia) HWP' HS' Hib' ltac:(rewrite El', <- El; exact Eb)).
Qed.

Lemma dl_from_Q0 : forall j Σk b ib ents rest, ents <> [] -> rt_wfP Σk ((b, ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
cps asegs (ASTA RTA Σk PMc (dl_Q p j b ents 0 rest Σk))
(fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
intros j Σk b ib ents rest Hne HWP HS Hib Eb. pose proof HS as (El & _).
destruct ents as [|e es]; [congruence|].
eapply (cps_seq asegs); [exact (ITEM j Σk b ib (e :: es) 0 rest ltac:(cbn; lia) HWP HS Hib Eb)|].
apply dl_cps_ex. intros Σk' (HWP' & HS' & Hib'). pose proof HS' as (El' & _).
exact (dl_from_N (length es) j Σk' b ib (e :: es) 0 rest ltac:(cbn; lia) HWP' HS' Hib' ltac:(rewrite El', <- El; exact Eb)).
Qed.

Lemma dl_from_B : forall j rest Σk, rt_wfP Σk rest -> dl_sig p Σk -> cps asegs (ASTA RTA Σk PMc (dl_B p j rest Σk)) FIN.
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
intros j. induction rest as [|[b ents] rest IH]; intros Σk HWP HS; pose proof HS as (El & _);
pose proof (geo_of_wfP _ _ HWP) as HG; pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _);
pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
-
eapply (cps_seq asegs).
+ apply (dl_evt Σk PMc _ (dl_R p Σk) MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
pose proof DM as (A & MI & ST & WM0 & RP & _).
eapply evt_mono; [apply (drec_loop_ret_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2056) j
(Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
(dl_r8 p) (dl_r9 p))|].
1: exact (dl_drec j Σk [] m DM El). 1: exact ST. 1: lia. 1: exact N4. 1: exact N6. 1: exact MI.
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & QR' & ST').
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
split; [exact (artc_stk Σk m m' [] lo (C + 32) HG HL (Forall_nil _) A Hdep (hqb_of_wfP _ _ HWP) MU WM)|].
split; [exact MI'|]. split; [exact ST'|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|]. split; [|exact QR'].
pose proof (client_stk Σk m m' [] lo (C + 32) HG HL ltac:(lia) (Forall_nil _) Hlive MU) as RP'.
pose proof HS as (_ & Elv & Efr & _). rewrite Elv, Efr in RP'.
intros a Ha. rewrite (RP' a Ha). exact (RP a Ha).
+ intros T0 cf Hcf Hk. apply Hk. exists Σk. split; [exact Hcf | split; [exact HWP | exact HS]].
- destruct (dl_batch_of Σk b ents rest HWP) as (ib & Hib & Eb).
pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4).
assert (QW : qwf SB ((b, ents) :: rest)) by (pose proof (qwf_of_wfP _ _ HWP) as X; rewrite El in X; exact X).
assert (QB : X0fy.qbytes ((b, ents) :: rest) <= 2 ^ 40) by (destruct HWP as (_ & _ & _ & _ & (_ & _ & X & _) & _); exact X).
rewrite qbytes_eq in QB.
destruct ents as [|e es].
+
eapply (cps_seq asegs); [| eapply (cps_seq asegs); [exact (BATCH j Σk b ib [] rest HWP HS Hib Eb)|]].
* apply (dl_evt Σk PMc _ _ MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
pose proof DM as (_ & MI & ST & _).
eapply evt_mono; [apply (drec_loop_deal_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (usp - 2056)
j (Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p)
(dl_r7 p) (dl_r8 p) (dl_r9 p) b rest)|].
1: exact QW. 1: lia. 1: exact N2. 1: lia. 1: exact (dl_drec j Σk _ m DM El). 1: exact ST. 1: exact N3. 1: lia. 1: lia. 1: exact MI.
intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
exact (dl_mem_step j Σk _ rest m m' [(C, C + 32)] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP)
ltac:(repeat constructor; cbn [fst snd]; lia) MU WM MI' ST' DM').
* apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (IH Σk' HWP' HS').
+
eapply (cps_seq asegs); [| eapply (cps_seq asegs); [exact (dl_from_Q0 j Σk b ib (e :: es) rest ltac:(discriminate) HWP HS Hib Eb)|]].
* apply (dl_evt Σk PMc _ _ MST).
intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
pose proof DM as (_ & MI & ST & _).
eapply evt_mono; [apply (drec_loop_qcb_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2056)
j (Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p)
(dl_r7 p) (dl_r8 p) (dl_r9 p) b (e :: es) rest)|].
1: discriminate. 1: exact QW. 1: lia. 1: exact N1. 1: exact (dl_drec j Σk _ m DM El). 1: exact ST. 1: exact N3. 1: lia. 1: lia. 1: exact MI.
intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
exact (dl_mem_step j Σk _ rest m m' [(C, C + 32)] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP)
ltac:(repeat constructor; cbn [fst snd]; lia) MU WM MI' ST' DM').
* apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (IH Σk' HWP' HS').
Qed.

End DLoop.
End RL_drain_loop.
Export RL_drain_loop.

Module RL_drain_itemp.
Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0ib X0hx X0hv X0gj X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0df X0g3 X0ci X0cr X0cp X0cn X0ca X0ck X0cs X0ce X0cd.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop.

Lemma skipn_nth_cons : forall {X} (l : list X) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof. intros X l. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma cps_pointwise : forall (Σ : rtsA) (PMc : Model -> Prop) (Pm : machine_state -> Prop) (Q : config -> Prop),
(forall ms, Pm ms -> cps asegs (ASTA RTA Σ PMc (eq ms)) Q) -> cps asegs (ASTA RTA Σ PMc Pm) Q.
Proof.
intros Σ PMc Pm Q H T cf (H1 & H2 & H3 & H4) Hk. apply (H _ H2 T cf); [|exact Hk].
split; [exact H1|]. split; [reflexivity|]. split; [exact H3 | exact H4].
Qed.

Lemma pres_munch : forall L F z (m m' : mem), rt_pres L F z m m' -> munch [(0, z); (USTACK_TOP, 2 ^ 64)] m m'.
Proof.
intros L F z m m' H x Hx. apply H. cbn [outside] in Hx. left.
pose proof (bv_unsigned_in_range 64 x) as X. unfold bv_modulus in X. cbn [Z.of_N] in X. lia.
Qed.

Lemma rt_pres_mono : forall L F z z' (m m' : mem), rt_pres L F z m m' -> z <= z' -> rt_pres L F z' m m'.
Proof. intros L F z z' m m' H Hz a Ha. apply H. destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha]. Qed.

Lemma rt_pres_trans : forall L F z (m1 m2 m3 : mem), rt_pres L F z m1 m2 -> rt_pres L F z m2 m3 -> rt_pres L F z m1 m3.
Proof. intros L F z m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Section IpGeo.
Variables (Σ : rtsA) (c : Z) (ic : nat) (n C lo : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hic : nth_error (r_st (pr Σ c)) ic = Some (CkQuar n).
Hypothesis HL1 : l_ACEIL (lay Σ) <= lo.
Hypothesis HL2 : lo <= C - 1136.
Hypothesis HL3 : C <= 2 ^ 47.
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c ic).
#[local] Notation W12 := (W_QCB (p_abeg (l_SB (lay Σ)) c ic) (p_abeg (l_SB (lay Σ)) c ic + rz_size n - 16) n (l_T (lay Σ)) C
++ W_CD (l_T (lay Σ)) (l_SB (lay Σ)) c (C - 112)).

Lemma ip_facts : AB + 8 <= AB + ClassSize c /\ AB <= AB + rz_size n - 16 /\ AB + rz_size n - 16 + 4 <= AB + ClassSize c
/\ SHB <= shad (AB + rz_size n - 16 + 16) /\ shad (AB + rz_size n - 16 + 16) + ru8 n / 8 <= 2 ^ 44 + SHB
/\ SHB <= shad (rb SB c + kUserCap) /\ shad (rb SB c + 2 ^ 32) <= 2 ^ 44 + SHB
/\ AB + ClassSize c <= SB + 2 ^ 37 /\ 0 <= AB.
Proof using HG Hc Hic.
clear HL1 HL2 HL3. pose proof (qp_fit Σ c ic n HG Hc Hic) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
pose proof (qp_slot Σ c ic n HG Hc Hic) as (P1 & P2 & P3 & P4 & P5 & G1 & G2 & G3).
pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4). pose proof (dk_geo Σ HG) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
pose proof (shad_len (AB + rz_size n - 16 + 16) (ru8 n) ltac:(lia) ltac:(lia) ltac:(lia)) as (SL1 & SL2).
assert (Z.max 0 (ru8 n / 8) = ru8 n / 8) by (apply Z.max_r; apply Z.div_pos; lia).
pose proof (shad_len (rb SB c + kUserCap) (2 ^ 32 - kUserCap) ltac:(unfold rb, kUserCap in *; lia) ltac:(unfold kUserCap; lia)
ltac:(unfold rb, kUserCap in *; lia)) as (SL3 & _).
pose proof (fk_shad_mono (rb SB c + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
repeat split; lia.
Qed.

Lemma ip_batch_av : forall j', nth_error (r_st (pr Σ 24)) j' = Some CkBatch -> disjoint_from W12 (p_abeg SB 24 j') 8192.
Proof using HG Hc Hic HL1 HL2 HL3.
intros j' Hj.
pose proof ip_facts as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
pose proof (g_slot_apart Σ HG c ic 24 j' _ _ Hc ltac:(lia) Hic Hj
ltac:(destruct (Z.eq_dec c 24) as [->|X]; [right; intros <-; rewrite Hic in Hj; discriminate | left; exact X])) as AP.
change (ClassSize 24) with 8192 in AP.
pose proof (dk_slot_in Σ HG 24 j' _ ltac:(lia) Hj) as (U1 & U2 & U3 & U4 & U5 & U6). change (ClassSize 24) with 8192 in *.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5). pose proof HSB as (Y1 & Y2 & Y3 & Y4).
assert (HTT : T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
unfold W_QCB, W_CD. cbn [app disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB, kHighShadowEnd in *.
repeat split; lia.
Qed.

Lemma ip_stack_av : forall a k, C - 112 <= a -> 0 <= k -> disjoint_from W12 a k.
Proof using HG Hc Hic HL1 HL2 HL3.
intros a k Ha Hk.
pose proof ip_facts as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5).
unfold W_QCB, W_CD. cbn [app disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
repeat split; lia.
Qed.

End IpGeo.

Lemma dl_batch_of_in : forall Σk P b' ents', rt_wfP Σk P -> In (b', ents') P ->
exists j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch /\ b' = p_abeg (l_SB (lay Σk)) 24 j'.
Proof.
intros Σk P b' ents' (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _) Hin. unfold qallP in Q4.
assert (Hb : In (b', ents') (ql Σk ++ qg Σk ++ P)) by (apply in_app_iff; right; apply in_app_iff; right; exact Hin).
destruct (proj1 (Forall_forall _ _) Q4 _ Hb) as (j' & Hj & Eb). exists j'. split; [exact Hj | exact Eb].
Qed.

Section ItemP.
Variable p : dlp.
Hypothesis FC : fixed_commit_node.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).

Theorem item_prim_ok : item_prim_stmt p.
Proof using FC HOK.
intros j Σk b ib ents i rest c ic n Hi HWP HS Hib Eb Hc Hic Hent.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & HR & Hlive & HSW & HQW & HFW & HB & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
pose proof (proj1 (proj2 (proj2 HR)) c Hc) as (Hcnt & _ & Hcl0).
assert (Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σk c)))) (ca Σk c)) by (eapply Forall_impl; [|exact Hcl0]; intros x (X & _); exact X).
pose proof (proj1 HR c Hc) as HRW.
assert (HAw : A_bytes (aw Σk) <= CREDIT0) by (destruct HB as (X1 & _ & X3 & _); lia).
assert (HEg : rt_eager (recp Σk c ic) <= 2 ^ 38)
by (exact (proj1 (proj2 (proj2 (proj2 (budget_wf_recp Σk c ic (CkQuar n) HB HR HSW Hc Hic ltac:(discriminate) Einit)))))).

assert (Esk : skipn i ents = (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16, n) :: skipn (S i) ents)
by (rewrite (skipn_nth_cons ents i (0, 0) Hi), Hent; reflexivity).
rewrite Esk in HWP.
pose proof (rt_wfP_recp Σk b _ n (skipn (S i) ents) rest c ic HWP Hc Hic eq_refl Einit) as HWP'.
apply cps_pointwise. intros ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof FR as (FR1 & FR2 & FR3). pose proof FR2 as CBP0.
apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 (l_T (lay Σ0) + 208))] [C8 (Z_to_bv 64 (usp - 2056))])) in CBP0.
destruct CBP0 as (CBP & _). rewrite <- El in CBP.
rewrite Hent. cbn [fst].
eapply (cps_seq asegs).
{ eapply (dl_evt Σk PMc _ _ MST). intros ms0 <-.
exact (qcbp_evt Σk m C lo c ic n (dl_gp p) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1023064)
(Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) HG HA Hc Hic CBP ST HLk ltac:(lia) ltac:(lia) MI Hlive Hdep HQB). }
apply cps_pointwise. intros ms1 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & HA1 & MU1 & WM1 & MI1 & ST1 & RP1).
assert (Esp : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
eapply (cps_conseq asegs).
- exact (cd_lift Σk PMc m1 c ic (CkQuar n) lo (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' (Z_to_bv 64 C)
(Z_to_bv 64 INST) a4' a5' a6' a7' (Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37))
(Z_to_bv 64 (Z.of_nat (length ents))) (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16))
(Z_to_bv 64 (16 + Z.of_nat i)) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p)
FDO MST FC HG HA1 Hc Hic Einit HRW Hcl Hcnt ltac:(rewrite Esp; exact ST1) HLk ltac:(rewrite Esp; lia) ltac:(rewrite Esp; lia)
MI1 Hlive Hdep HQB HL HAw HEg).
- intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms E; rewrite <- E; reflexivity | intros mo X; exact X].
- intros cf Hcf. exists (recp Σk c ic). split.
+ unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & HA2 & MU2 & WM2 & MI2 & ST2 & RP2).
rewrite Esp in MU2, ST2, RP2.
rewrite (ret_pc_even 0x47e7c); [| lia | reflexivity].
exists (Z_to_bv 64 0x47e7c), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
assert (RPa : rt_pres (live Σ0) (frames Σ0) (C - 112) m m2).
{ rewrite <- Elv, <- Efr. exact (rt_pres_trans _ _ _ m m1 m2 RP1 RP2). }
pose proof (pres_munch _ _ _ m m2 RPa) as MUa.
assert (WMa : wmono asegs m m2) by exact (wmono_trans _ _ _ _ WM1 WM2).
assert (MUb : munch (W_QCB (p_abeg (l_SB (lay Σk)) c ic) (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16) n (l_T (lay Σk)) C
++ W_CD (l_T (lay Σk)) (l_SB (lay Σk)) c (C - 112)) m m2).
{ apply (munch_trans _ m m1 m2); eapply munch_weaken; [| exact MU1 | | exact MU2]; intros x Hx; apply outside_app_inv in Hx; destruct Hx as [Hx1 Hx2]; first [exact Hx1 | exact Hx2]. }
assert (HBAV : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from (W_QCB (p_abeg (l_SB (lay Σk)) c ic)
(p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16) n (l_T (lay Σk)) C ++ W_CD (l_T (lay Σk)) (l_SB (lay Σk)) c (C - 112))
(p_abeg (l_SB (lay Σk)) 24 j') 8192)
by exact (ip_batch_av Σk c ic n C lo HG Hc Hic HLk ltac:(lia) ltac:(lia)).
split.
* split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m2 WG WMa) | exact HGo]|].
split; [exact (rt_pres_trans _ _ _ _ m m2 RP (rt_pres_mono _ _ (C - 112) (C + 32) m m2 RPa ltac:(lia)))|].
split.
-- split; [|split].
++ apply (rw_cells_transport asegs _ m m2 _ _ FR1 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
++ apply (rw_cells_transport asegs _ m m2 _ _ FR2 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
++ apply (rw_cells_transport asegs _ m m2 _ _ FR3 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (qcache_rep_frame _ m m2 C rest QR MUb WMa).
++ exact (ip_stack_av Σk c ic n C lo HG Hc Hic HLk ltac:(lia) ltac:(lia) C 32 ltac:(lia) ltac:(lia)).
++ apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (HBAV j' Hj').
* apply (qbatch_frame _ m m2 b (qfirst rest) ents QB MUb WMa). rewrite Eb. exact (HBAV ib Hib).
+ split; [exact HWP'|]. split.
* pose proof (recp_fields Σk c ic) as (X1 & X2 & _ & _ & _ & X6 & _ & _ & _ & _ & _ & X12 & X13 & X14).
split; [rewrite X1; exact El|]. split; [rewrite X13; exact Elv|]. split; [rewrite X14; exact Efr|].
split; [rewrite X12; exact Ecr|]. split; [rewrite X6; exact Eql | split; [rewrite X2; exact Einit | exact Epo]].
* rewrite recp_st. destruct (Z.eqb_spec 24 c) as [E24|N24]; cbn [andb]; [|exact Hib].
destruct (Nat.eqb_spec ic ib) as [<-|X]; [| exact Hib]. rewrite <- E24 in Hic. rewrite Hic in Hib. discriminate.
Qed.

End ItemP.
End RL_drain_itemp.
Export RL_drain_itemp.

Module RL_drain_batch.
Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0ib X0hx X0hv X0gj X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0df X0g3 X0ci X0cr X0cp X0cn X0ca X0ck X0ce X0cd.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp.

Lemma stk_of_bytes_wr : forall (m : mem) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) ->
stk asegs m a (a + Z.of_nat (length bs)).
Proof.
intros m a bs (B0 & B1 & Hb) (W0 & W1 & Hw). split; [exact B0|]. split; [lia|]. intros x Hx.
split; [replace x with (a + (x - a)) by lia; apply Hw; lia|].
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite Hb by lia.
destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma qbatch_stk : forall (m : mem) b nxt ents, qbatch m b nxt ents -> stk asegs m b (b + 8192).
Proof.
intros m b nxt ents (H & (ws & U & Hl & _) & _).
destruct H as ((_ & Hb) & Hw). cbn [cells_bytes cbytes] in Hb. rewrite !app_nil_r in Hb.
pose proof (stk_of_bytes_wr m b _ Hb ltac:(rewrite !length_app, !length_le8; exact Hw)) as S1.
rewrite !length_app, !length_le8 in S1. change (Z.of_nat (8 + (8 + 8))) with 24 in S1.
destruct U as (Ub & Uw). pose proof (stk_of_bytes_wr m (b + 0x18) _ Ub ltac:(rewrite u64s_length, Nat2Z.inj_mul; exact Uw)) as S2.
rewrite u64s_length, Hl in S2. change (Z.of_nat (8 * 1021)) with 8168 in S2.
destruct S1 as (A0 & A1 & Aw). destruct S2 as (C0 & C1 & Cw). split; [lia|]. split; [lia|]. intros x Hx.
destruct (Z_lt_ge_dec x (b + 24)) as [X|X]; [apply Aw; lia | apply Cw; lia].
Qed.

Lemma artc_unbatch : forall (Σ : rtsA) (m : mem) ib, ARTc Σ m -> nth_error (r_st (pr Σ 24)) ib = Some CkBatch ->
stk asegs m (p_abeg (l_SB (lay Σ)) 24 ib) (p_abeg (l_SB (lay Σ)) 24 ib + 8192) -> ARTc (set_st Σ 24 ib CkIdle) m.
Proof.
intros Σ m ib HA Hib ST. destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
apply ARTc_intro.
- exact A1.
- intros c' Hc'. destruct (Z.eq_dec c' 24) as [->|Hne].
+ rewrite set_st_pr_same'. apply reg_rep_ureg'. exact (A2 24 Hc').
+ rewrite (set_st_pr_other' Σ 24 ib CkIdle c' Hne). exact (A2 c' Hc').
- exact A3.
- destruct A4 as [P Sc]. split; [|exact Sc].
intros c' i' st Hc' Hn'. destruct (Z.eq_dec c' 24) as [->|Hne].
+ rewrite set_st_pr_same' in Hn'. unfold ureg in Hn'. cbn [r_st] in Hn'. rewrite nth_upd_ck in Hn'.
destruct (Nat.eqb_spec ib i') as [<-|Hii].
* destruct (Nat.ltb_spec ib (length (r_st (pr Σ 24)))); [|discriminate]. injection Hn' as <-.
pose proof (P 24 ib CkBatch Hc' Hib) as X. cbn [pchunk] in X |- *. split; [exact ST | exact X].
* exact (P 24 i' st Hc' Hn').
+ rewrite (set_st_pr_other' Σ 24 ib CkIdle c' Hne) in Hn'. exact (P c' i' st Hc' Hn').
- exact A5.
- exact A6.
- exact A7.
- exact A8.
- exact A9.
- exact A10.
- exact A11.
Qed.

Lemma bt_batch_av : forall (Σ : rtsA) j' C lo, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j' = Some CkBatch ->
l_ACEIL (lay Σ) <= lo -> lo <= C - 1136 -> C <= 2 ^ 47 ->
disjoint_from (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) 24 (C - 112)) (p_abeg (l_SB (lay Σ)) 24 j') 8192.
Proof.
intros Σ j' C lo HG Hj HL1 HL2 HL3.
pose proof (dk_slot_in Σ HG 24 j' _ ltac:(lia) Hj) as (U1 & U2 & U3 & U4 & U5 & U6). change (ClassSize 24) with 8192 in *.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG 24 ltac:(lia)) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5). pose proof HSB as (Y1 & Y2 & Y3 & Y4).
assert (HTT : l_T (lay Σ) + 4096 <= l_SB (lay Σ) \/ l_SB (lay Σ) + 2 ^ 37 + 4096 <= l_T (lay Σ)) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
pose proof (fk_shad_mono (rb (l_SB (lay Σ)) 24 + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB, kHighShadowEnd in *.
repeat split; lia.
Qed.

Lemma bt_stack_av : forall (Σ : rtsA) C lo a k, geo_ok Σ -> l_ACEIL (lay Σ) <= lo -> lo <= C - 1136 -> C <= 2 ^ 47 ->
C - 112 <= a -> 0 <= k -> disjoint_from (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) 24 (C - 112)) a k.
Proof.
intros Σ C lo a k HG HL1 HL2 HL3 Ha Hk.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG 24 ltac:(lia)) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5).
pose proof (fk_shad_mono (rb (l_SB (lay Σ)) 24 + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
repeat split; lia.
Qed.

Section Batch.
Variable p : dlp.
Hypothesis FC : fixed_commit_node.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).

Theorem batch_ok : batch_stmt p.
Proof using FC HOK.
intros j Σk b ib ents rest HWP HS Hib Eb.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & HR & Hlive & HSW & HQW & HFW & HB & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
pose proof (proj1 (proj2 (proj2 HR)) 24 ltac:(lia)) as (Hcnt & _ & Hcl0).
assert (Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σk 24)))) (ca Σk 24)) by (eapply Forall_impl; [|exact Hcl0]; intros x (X & _); exact X).
pose proof (proj1 HR 24 ltac:(lia)) as HRW.
assert (HAw : A_bytes (aw Σk) <= CREDIT0) by (destruct HB as (X1 & _ & X3 & _); lia).
assert (HEg : rt_eager (recp Σk 24 ib) <= 2 ^ 38)
by (exact (proj1 (proj2 (proj2 (proj2 (budget_wf_recp Σk 24 ib CkBatch HB HR HSW ltac:(lia) Hib ltac:(discriminate) Einit)))))).
pose proof (rt_wfP_batch Σk b rest ib HWP Hib Eb Einit) as HWP'.
apply cps_pointwise.
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof FR as (FR1 & FR2 & FR3).
assert (HA' : ARTc (set_st Σk 24 ib CkIdle) m).
{ apply (artc_unbatch Σk m ib HA Hib). rewrite <- Eb. exact (qbatch_stk m b _ ents QB). }
assert (Esp : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
eapply (cps_conseq asegs).
- exact (cd_lift Σk PMc m 24 ib CkBatch lo (Z_to_bv 64 0x47eb4) (Z_to_bv 64 (C - 112)) (dl_gp p) t0 t1 t2 (Z_to_bv 64 C)
(Z_to_bv 64 INST) a4 a5 a6 a7 (Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37))
s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p)
FDO MST FC HG HA' ltac:(lia) Hib Einit HRW Hcl Hcnt ltac:(rewrite Esp; exact ST) HLk ltac:(rewrite Esp; lia) ltac:(rewrite Esp; lia)
MI Hlive Hdep HQB HL HAw HEg).
- intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms E. rewrite <- E. unfold cd_msD. rewrite <- Eb, El. reflexivity.
- intros cf Hcf. exists (recp Σk 24 ib). split.
+ unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & HA2 & MU2 & WM2 & MI2 & ST2 & RP2).
rewrite Esp in MU2, ST2, RP2.
rewrite (ret_pc_even 0x47eb4); [| lia | reflexivity].
exists (Z_to_bv 64 0x47eb4), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', (Z_to_bv 64 b), s6, s7, s8, s9,
t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
assert (RPa : rt_pres (live Σ0) (frames Σ0) (C - 112) m m2) by (rewrite <- Elv, <- Efr; exact RP2).
pose proof (pres_munch _ _ _ m m2 RPa) as MUa.
split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m2 WG WM2) | exact HGo]|].
split; [exact (rt_pres_trans _ _ _ _ m m2 RP (rt_pres_mono _ _ (C - 112) (C + 32) m m2 RPa ltac:(lia)))|].
split.
* split; [|split].
-- apply (rw_cells_transport asegs _ m m2 _ _ FR1 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (rw_cells_transport asegs _ m m2 _ _ FR2 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (rw_cells_transport asegs _ m m2 _ _ FR3 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
* apply (qcache_rep_frame _ m m2 C rest QR MU2 WM2).
-- exact (bt_stack_av Σk C lo C 32 HG HLk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
-- apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'.
exact (bt_batch_av Σk j' C lo HG Hj' HLk ltac:(lia) ltac:(lia)).
+ split; [exact HWP'|].
pose proof (recp_fields Σk 24 ib) as (X1 & X2 & _ & _ & _ & X6 & _ & _ & _ & _ & _ & X12 & X13 & X14).
split; [rewrite X1; exact El|]. split; [rewrite X13; exact Elv|]. split; [rewrite X14; exact Efr|].
split; [rewrite X12; exact Ecr|]. split; [rewrite X6; exact Eql | split; [rewrite X2; exact Einit | exact Epo]].
Qed.

End Batch.
End RL_drain_batch.
Export RL_drain_batch.

Module RL_drain_rec.
Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0i7 X0ib X0hx X0hv X0gj X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0df X0g3 X0ci X0cr X0cp X0cv X0cn X0ck X0cb.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch.

Section DRec.
Variable p : dlp.
Hypothesis HOK : dl_ok p.
Hypothesis ITEM : item_stmt p.
Hypothesis BATCH : batch_stmt p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).

Definition dl_E (tmp : list batch) (Σk : rtsA) : machine_state -> Prop :=
fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
ms = MS (mkR (Z_to_bv 64 0x47bc0) (Z_to_bv 64 C) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) (Z_to_bv 64 QUAR)
(Z_to_bv 64 C) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp - 2056)) a4 a5 a6 a7 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p)
(dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 qdorec_entry) (dl_fc p) None m (seg_rom asegs)
/\ ARTc Σk m /\ qcache_rep m C tmp /\ stk asegs m lo C /\ mem_inv asegs m
/\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G) /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m.

Lemma dl_mem_entry : forall j Σk rest (m m' : mem) (W : list ivl), ARTc Σk m -> (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G) ->
rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m -> geo_ok Σk -> dl_sig p Σk ->
live_wf Σk -> depot_ok (dep Σk) (l_DNB (lay Σk)) (l_SSB (lay Σk)) (l_ACEIL (lay Σk)) ->
Forall (fun b => exists j, nth_error (r_st (pr Σk 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σk)) 24 j) (ql Σk ++ qg Σk) ->
Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) W -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (C - 112) ->
drec_mem m' C SB j (T + 208) (usp - 2056) (Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
(dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest ->
dl_mem p j Σk rest m'.
Proof using HOK.
intros j Σk rest m m' W A WM0 RP HG (El & Elv & Efr & _) Hlive Hdep HQB HW MU WM MI' ST' (FR' & _ & QR').
pose proof HOK as (_ & _ & HLO & HLO2 & HSP & HG0).
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
split; [exact (artc_stk Σk m m' W lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
split; [exact MI'|]. split; [exact ST'|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
split; [|split; [exact FR' | exact QR']].
pose proof (client_stk Σk m m' W lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
exact (rt_pres_trans _ _ _ _ m m' RP RP').
Qed.

Theorem dl_from_E : forall Σk tmp, rt_wfP Σk tmp -> dl_sig p Σk -> cps asegs (ASTA RTA Σk PMc (dl_E tmp Σk)) (dl_fin p).
Proof using HOK ITEM BATCH.
intros Σk tmp HWP HS.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof HS as (El & Elv & Efr & _).
pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
destruct tmp as [|[b ents] rest].
-
eapply (cps_seq asegs).
+ apply (dl_evt Σk PMc _ (dl_R p Σk) MST).
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
eapply evt_mono; [apply (drec_empty_spec (Z_to_bv 64 0x47bc0) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
(dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m C lo (T + 208) (usp - 2056))|].
1: exact QR. 1: exact ST. 1: lia. 1: exact N4. 1: exact N6. 1: exact N7. 1: exact N8. 1: exact MI.
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & QR' & ST').
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
assert (HW : Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) [(C - 112, C)]) by (repeat constructor; cbn [fst snd]; lia).
split; [exact (artc_stk Σk m m' _ lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
split; [exact MI'|]. split; [exact ST'|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
split; [|exact QR'].
pose proof (client_stk Σk m m' _ lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
exact (rt_pres_trans _ _ _ _ m m' RP RP').
+ intros T0 cf Hcf Hk. apply Hk. exists Σk. split; [exact Hcf | split; [exact HWP | exact HS]].
- destruct (dl_batch_of Σk b ents rest HWP) as (ib & Hib & Eb).
pose proof (dl_bslot p HLO HLO2 HSP HG0 Σk ib HG El Hib) as (B1 & B2 & B3 & B4).
assert (QW : qwf SB ((b, ents) :: rest)) by (pose proof (qwf_of_wfP _ _ HWP) as X; rewrite El in X; exact X).
assert (QB : X0fy.qbytes ((b, ents) :: rest) <= 2 ^ 40) by (destruct HWP as (_ & _ & _ & _ & (_ & _ & X & _) & _); exact X).
rewrite qbytes_eq in QB.
assert (HW : Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) [(C - 112, C + 32)]) by (repeat constructor; cbn [fst snd]; lia).
destruct ents as [|e es].
+
eapply (cps_seq asegs).
* apply (dl_evt Σk PMc _ (fun ms => exists j, dl_D p j b [] rest Σk ms) MST).
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
destruct IC1 as (SBC & _).
eapply evt_mono; [apply (drec_first_deal_spec (Z_to_bv 64 0x47bc0) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
(dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (usp - 2056) b rest)|].
1: exact QW. 1: lia. 1: exact N2. 1: exact QR. 1: exact SBC. 1: exact ST. 1: lia. 1: exact N3. 1: exact N4. 1: exact N6.
1: exact N7. 1: exact N8. 1: exact MI.
intros ms' (j & t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists j, t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
exact (dl_mem_entry j Σk rest m m' _ A WM0 RP HG HS Hlive Hdep HQB HW MU WM MI' ST' DM').
* apply cps_pointwise. intros ms (j & X).
eapply (cps_seq asegs).
-- eapply (cps_conseq asegs); [exact (BATCH j Σk b ib [] rest HWP HS Hib Eb) | | intros cf Hcf; exact Hcf].
intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms' <-; exact X | intros mo Y; exact Y].
-- apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (dl_from_B p MST HLO HLO2 HSP HG0 ITEM BATCH j rest Σk' HWP' HS').
+
eapply (cps_seq asegs).
* apply (dl_evt Σk PMc _ (fun ms => exists j, dl_Q p j b (e :: es) 0 rest Σk ms) MST).
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
destruct IC1 as (SBC & _).
eapply evt_mono; [apply (drec_first_qcb_spec (Z_to_bv 64 0x47bc0) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
(dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2056) b (e :: es) rest)|].
1: discriminate. 1: exact QW. 1: lia. 1: exact N1. 1: exact QR. 1: exact SBC. 1: exact ST. 1: lia. 1: exact N3. 1: exact N4. 1: exact N6.
1: exact N7. 1: exact N8. 1: exact MI.
intros ms' (j & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
exists j, t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
exact (dl_mem_entry j Σk rest m m' _ A WM0 RP HG HS Hlive Hdep HQB HW MU WM MI' ST' DM').
* apply cps_pointwise. intros ms (j & X).
eapply (cps_seq asegs).
-- eapply (cps_conseq asegs); [exact (dl_from_Q0 p MST HLO HLO2 HSP HG0 ITEM BATCH j Σk b ib (e :: es) rest ltac:(discriminate) HWP HS Hib Eb)
| | intros cf Hcf; exact Hcf].
intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms' <-; exact X | intros mo Y; exact Y].
-- apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (dl_from_B p MST HLO HLO2 HSP HG0 ITEM BATCH j rest Σk' HWP' HS').
Qed.

End DRec.
End RL_drain_rec.
Export RL_drain_rec.

Module RL_drain_xfer.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0hs X0id X0i7 X0hy X0ib X0fy X0fg X0da X0g4 X0d8 X0fq X0e4 X0e8 X0d9 X0e5 X0e6 X0df X0ci X0cr X0cp X0cv X0cn X0c8.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec.

Definition W_D (T usp : Z) (bw : list ivl) : list ivl :=
[(i_q_cmutex, i_q_cmutex + 4); (i_q_global, i_q_global + 32); (T + 80, T + 112)] ++ bw ++ [(usp - 2256, usp - 2208)].
Definition W_X (T usp : Z) (bw : list ivl) : list ivl := W_D T usp bw ++ [(usp - 2208, usp - 2128)].
Definition TZ_X (T : Z) : list ivl := [(T + 80, T + 112)].

Lemma xq_cells : forall Σ m, ARTc Σ m ->
qcache_rep m (l_T (lay Σ) + 80) (ql Σ) /\ qcache_rep m QG (qg Σ) /\ q_lock m 0 0
/\ rw_cells asegs m q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)].
Proof.
intros Σ m (A1 & _ & _ & _ & _ & (Q1 & Q2 & Q3) & _). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
destruct A1 as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
repeat match type of IC with _ /\ ?R => destruct IC as [?X IC] end.
match goal with H : rw_cells asegs m i_q_max _ |- _ => exact H end.
Qed.

Lemma qwf_of_wfx : forall Σ, rt_wfx Σ -> qwf (l_SB (lay Σ)) (qg Σ ++ ql Σ).
Proof.
intros Σ (H1 & HR & HV & HS & (Q1 & Q2 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & _).
assert (GQ : Permutation (ql Σ ++ qg Σ) (qg Σ ++ ql Σ)) by apply Permutation_app_comm.
split; [apply (Permutation_NoDup (Permutation_map fst GQ)); apply NoDup_ListNoDup; exact Q5|].
apply (Permutation_Forall GQ). apply Forall_forall. intros b Hb.
destruct (proj1 (Forall_forall _ _) Q4 b Hb) as (i & Hi & Eb). pose proof (proj1 (Forall_forall _ _) Q6 b Hb) as Hl.
pose proof HR as (HR1 & _). pose proof (HR1 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W11).
pose proof H1 as (_ & _ & _ & _ & _ & HSB & _). change (ClassSize 24) with 8192 in W11.
assert (Hlt : (i < length (r_st (pr Σ 24)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
unfold p_abeg in Eb. change (ClassSize 24) with 8192 in Eb. unfold r24.
split; [rewrite Eb; apply Z.mod_divide; [lia|]; apply Z.mod_divide in HSB; [|lia]; destruct HSB as (q & Hq);
exists (q * 8 + 24 * 2 ^ 19 + Z.of_nat i); lia|].
split; [lia|]. split; [lia|]. split; [exact Hl|].
apply Forall_forall. intros e He.
assert (Hq : In e (qents Σ)) by (unfold qents; apply in_flat_map; exists b; split; [exact Hb | exact He]).
pose proof (qent_n_pos Σ e HR HS (proj1 (Forall_forall _ _) Q7 e Hq)). lia.
Qed.

Definition dpost (F : bvmap 5 word) (fc : bv 32) (Σ' : rtsA) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (live0 : list (Z * Z))
(frames0 : list (Z * nat)) (m : mem) : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x46714) fc None m' (seg_rom asegs)
/\ ART_A Σ' m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (usp + -2128) /\ rt_pres live0 frames0 (usp + -2128) m m'.

Section XRun.
Variables (Σ : rtsA) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word).
Hypothesis HA : ARTc Σ m.
Hypothesis HW : rt_wfx Σ.
Hypothesis HC : rt_count Σ.
Hypothesis HBY : 0x100000 < X0fy.qbytes (ql Σ).
Hypothesis FR : qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714)
w0 w1 w2 w3 w4 w5 s6.
Hypothesis ST : stk asegs m lo (usp + -2208).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x4000 <= usp + -2208.
Hypothesis HSP : usp <= 2 ^ 47.
Hypothesis MI : mem_inv asegs m.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma xr_geo : geo_ok Σ /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T)
/\ (T + 4096 <= r24 SB \/ r24 SB + 2 ^ 32 <= T) /\ 0 < SB /\ r24 SB + 2 ^ 32 <= l_ACEIL L /\ 2 ^ 44 + SHB <= l_ACEIL L
/\ l_ACEIL L <= 2 ^ 47.
Proof using HW.
clear - HW.
assert (HG : geo_ok Σ) by (destruct HW as (H1 & H2 & _ & H4 & _ & H6 & _); exact (conj H1 (conj H2 (conj H4 H6)))).
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof (dk_T Σ HG) as (T1 & T2 & T3 & T4 & T5).
unfold r24. split; [exact HG|]. repeat split; try lia.
Qed.

Definition xms0 : machine_state :=
MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR) (Z_to_bv 64 (l_T (lay Σ) + 80))
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4a148) fc None m (seg_rom asegs).

Lemma xr_bytes : 0x100000 < X0id.qbytes (ql Σ) < 2 ^ 63.
Proof using HW HBY.
clear - HW HBY. rewrite <- qbytes_eq. destruct HW as (_ & _ & _ & _ & (Q1 & _) & _). unfold QMAX_L in Q1. lia.
Qed.

Definition xr_dentry (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) : machine_state :=
MS (mkR (Z_to_bv 64 0x4a080) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) a4' a5' a6' a7'
s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 qdrain_entry) fc None m (seg_rom asegs).

Lemma xr_head : evt asegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = xr_dentry t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6') xms0.
Proof using HA HW HBY FR ST HLO HLO2 HSP MI.
pose proof (xq_cells Σ m HA) as (QT & _). apply (proj1 (qcache_rep_iff _ _ _)) in QT. destruct QT as (QH & _).
pose proof xr_bytes as HB. pose proof xr_geo as (_ & X1 & X2 & _ & _ & _ & _ & X8 & X9).
assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
unfold xms0. replace (usp + -2208) with (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80) by (rewrite Esp; lia).
eapply evt_mono; [apply (qput_B_drain_spec (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2 s3 s4 s5
a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 s6 ra0 F fc m (T + 80) (T + 208)
(usp + -2056) (X0id.qbytes (ql Σ)) lo _ _ _ QH HB); [| exact MI]|].
- rewrite Esp. replace (usp + -2128 - 80) with (usp + -2208) by lia. exact FR.
- intros ms (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). rewrite Esp. replace (usp + -2128 + -80) with (usp + -2208) by lia.
exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6'. reflexivity.
Qed.

Lemma xr_quar : forall (m2 m3 : mem) G, qcache_rep m2 QG G -> qcache_rep m2 (T + 80) [] -> q_lock m2 0 0 ->
Forall (fun e => r24 SB <= fst e /\ fst e + 8192 <= r24 SB + 2 ^ 32) G ->
munch [(usp + -2208, usp + -2128)] m2 m3 -> wmono asegs m2 m3 -> quar_rep (set_q Σ [] G) m3.
Proof using HW HLO HLO2.
intros m2 m3 G QG2 QT2 LK2 RG MU WM. pose proof xr_geo as (_ & X1 & X2 & _ & _ & X6 & X7 & X8 & X9). unfold SHB in X8.
unfold quar_rep. cbn [lay ql qg set_q].
split; [apply (qcache_rep_frame _ m2 m3 _ _ QT2 MU WM); [cbn [disjoint_from]; unfold qcacheT; lia | constructor]|].
split; [apply (qcache_rep_frame _ m2 m3 _ _ QG2 MU WM); [cbn [disjoint_from]; lia|];
apply Forall_forall; intros e He; pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2); cbn [disjoint_from]; lia|].
unfold q_lock in LK2. apply (rw_cells_transport asegs _ m2 m3 _ _ LK2 MU WM). cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
unfold i_q_cmutex, INST, g_instance. lia.
Qed.

Lemma xr_cert : forall bw D, Forall (fun iv => exists c i, In (c, i) D /\ p_abeg SB c i <= fst iv /\ snd iv <= p_abeg SB c i + ClassSize c) bw ->
Forall (dzone Σ D [] [] (TZ_X T) IZ_Q [] lo (usp + -2128)) (W_X T usp bw).
Proof using HLO2.
intros bw D HB. unfold W_X, W_D. rewrite <- !app_assoc. apply Forall_app. split; [|apply Forall_app; split].
- constructor; [left; exists (i_q_cmutex, i_q_cmutex + 4); split; [left; reflexivity | cbn; lia]|].
constructor; [left; exists (i_q_global, i_q_global + 32); split; [right; left; reflexivity | cbn; lia]|].
constructor; [right; left; exists (T + 80, T + 112); split; [left; reflexivity | cbn; lia] | constructor].
- apply Forall_forall. intros iv Hiv. right; right; left. exact (proj1 (Forall_forall _ _) HB iv Hiv).
- constructor; [do 9 right; cbn; lia | constructor; [do 9 right; cbn; lia | constructor]].
Qed.

Lemma xr_TZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_X T)
/\ disjoint_from (TZ_X T) T 0x30 /\ disjoint_from (TZ_X T) (T + 48) 16 /\ disjoint_from (TZ_X T) (T + 0xc60) 1
/\ (forall c, 1 <= c <= 31 -> disjoint_from (TZ_X T) (pc_addr T c) 80).
Proof.
unfold TZ_X. split; [repeat constructor; cbn; lia|]. cbn [disjoint_from]. split; [split; [lia | exact I]|].
split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|]. intros c Hc. unfold pc_addr. split; [lia | exact I].
Qed.

Lemma xr_tail : forall bw D (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem),
(forall c i, In (c, i) D -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch) ->
Forall (fun iv => exists c i, In (c, i) D /\ p_abeg SB c i <= fst iv /\ snd iv <= p_abeg SB c i + ClassSize c) bw ->
munch (W_D T usp bw) m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
qcache_rep m2 QG (qg Σ ++ ql Σ) -> qcache_rep m2 (T + 80) [] -> q_lock m2 0 0 -> stk asegs m2 lo (usp + -2208) ->
X0id.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
evt asegs (dpost F fc (set_q Σ [] (qg Σ ++ ql Σ)) gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m)
(MS (mkR (Z_to_bv 64 0x4a080) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc (Z_to_bv 64 0x4a080)) fc None m2 (seg_rom asegs)).
Proof using HA HW HC FR ST HLO HLO2 HSP MI.
intros bw D t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 HD HB MU2 WM2 MI2 QG2 QT2 LK2 ST2 HBYg.
pose proof xr_geo as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
rewrite (ret_pc_even 0x4a080) by (first [reflexivity | lia]).
replace (usp + -2208) with (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80) by (rewrite Esp; lia).

assert (FR2 : qput_frame m2 (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6).
{ rewrite Esp. replace (usp + -2128 - 80) with (usp + -2208) by lia. unfold qput_frame in *.
apply (rw_cells_transport asegs _ m m2 _ _ FR MU2 WM2). cbn [cells_size csize Nat.add Z.of_nat].
unfold W_D. apply dsj_app; [cbn [disjoint_from]; unfold i_q_cmutex, i_q_global, INST, g_instance; repeat split; lia|].
apply dsj_app; [|cbn [disjoint_from]; repeat split; lia].
apply dsj_forall. apply Forall_forall. intros iv Hiv. destruct (proj1 (Forall_forall _ _) HB iv Hiv) as (c & i & HDi & E1 & E2).
destruct (HD c i HDi) as (-> & Hb). pose proof (dk_slot_in Σ HG 24 i CkBatch ltac:(lia) Hb) as (S1 & S2 & _).
pose proof (dk_geo Σ HG) as (_ & _ & _ & G4 & _ & _ & G7 & _). lia. }
assert (ST2' : stk asegs m2 lo (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80)) by (rewrite Esp; replace (usp + -2128 - 80) with (usp + -2208) by lia; exact ST2).
eapply evt_mono; [apply (qput_C_spec (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 t3' t4' t5' t6' (Z_to_bv 64 0x4a080) w0 w1 w2 w3 w4 w5 s6
(Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) F fc m2 lo FR2 ST2'); [rewrite Esp; lia | unfold SEGTOP_A in *; lia | exact MI2]|].
intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
rewrite Esp in MU3, ST3. replace (usp + -2128 - 80) with (usp + -2208) in MU3 by lia.
rewrite (ret_pc_even 0x46714) by (first [reflexivity | lia]).

assert (MU : munch (W_X T usp bw) m m3).
{ apply (munch_trans _ m m2 m3); [apply (munch_weaken (W_D T usp bw)); [|exact MU2] | apply (munch_weaken [(usp + -2208, usp + -2128)]); [|exact MU3]].
- intros x Hx. unfold W_X in Hx. apply (proj1 (X0i8.outside_app _ _ _)) in Hx. exact (proj1 Hx).
- intros x Hx. unfold W_X in Hx. apply (proj1 (X0i8.outside_app _ _ _)) in Hx. destruct Hx as (_ & Hx). cbn [outside] in Hx |- *. lia. }
assert (WM : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM2 WM3).
pose proof (xr_cert bw D HB) as CERT. pose proof xr_TZ as (TZ1 & TZ2).
assert (HD' : forall c i, In (c, i) D -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch) by exact HD.
pose proof HW as (_ & _ & HV & _ & _ & _ & _ & Hdep & _).
assert (HQ : quar_rep (set_q Σ [] (qg Σ ++ ql Σ)) m3).
{ apply (xr_quar m2 m3 _ QG2 QT2 LK2); [|exact MU3 | exact WM3].
pose proof (qwf_region _ _ (qwf_of_wfx Σ HW)) as RG. exact RG. }
unfold dpost. exists u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m3. split; [reflexivity|].
split; [apply c_ART; [exact (rt_wf_transfer Σ HW HC ltac:(rewrite qbytes_eq; unfold QMAX_G; lia)) |]
| split; [exact MI3 | split; [exact WM | split; [exact ST3|]]]].
- exact (artc_q Σ m m3 (W_X T usp bw) D (TZ_X T) lo (usp + -2128) [] (qg Σ ++ ql Σ) HG HD' TZ1 TZ2 HLO CERT HA Hdep MU WM HQ).
- exact (client_q Σ m m3 (W_X T usp bw) D (TZ_X T) lo (usp + -2128) HG HD' TZ1 HLO ltac:(clear - HLO2; lia) CERT HV MU).
Qed.

Theorem xfer_evt : X0id.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
evt asegs (dpost F fc (set_q Σ [] (qg Σ ++ ql Σ)) gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m) xms0.
Proof using HA HW HC HBY FR ST HLO HLO2 HSP MI.
intros HBYg. pose proof xr_geo as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
pose proof (xq_cells Σ m HA) as (QT & QGr & LK & QM).
apply (proj1 (rwc_app asegs m q_max [C8 (Z_to_bv 64 0x10000000)] [C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)])) in QM.
destruct QM as (QM & _).
pose proof (qwf_of_wfx Σ HW) as WF.
assert (Hne : ql Σ <> []) by (intros E; pose proof HBY as X; rewrite E in X; change (X0fy.qbytes []) with 0 in X; lia).
assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
assert (STd : stk asegs m lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST).
eapply evt_cut; [exact xr_head|]. intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). unfold xr_dentry.
assert (CASE : qg Σ = [] \/ exists pre bl el, qg Σ = pre ++ [(bl, el)]).
{ destruct (qg Σ) as [|b0 rest] eqn:E; [left; reflexivity | right].
destruct (exists_last (l := b0 :: rest) ltac:(discriminate)) as (pre & (bl & el) & E2). exists pre, bl, el. exact E2. }
destruct CASE as [EQG|(pre & bl & el & EQG)].
-
pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYg as HBYg'. rewrite EQG in QGr', WF', HBYg'. cbn [app] in WF', HBYg'.
eapply evt_cut; [apply (qdrain_ret_empty_spec (Z_to_bv 64 0x4a080) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2056) lo (ql Σ) Hne QGr' QT WF' HBYg' LK QM);
try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia); [exact STd | exact MI]|].
intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
rewrite Esp in MU2, ST2.
apply (xr_tail [] [] u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 (fun c i X => False_ind _ X) (Forall_nil _)); try assumption.
+ eapply munch_weaken; [|exact MU2]. unfold W_D, i_q_cmutex, i_q_global, INST, g_instance. cbn [app]. solve_sub_fp.
+ rewrite EQG. exact QG2.
-
pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYg as HBYg'. rewrite EQG in QGr', WF', HBYg'.
assert (Hbl : exists ib, nth_error (r_st (pr Σ 24)) ib = Some CkBatch /\ bl = p_abeg SB 24 ib).
{ destruct HW as (_ & _ & _ & _ & (_ & _ & Q4 & _) & _). rewrite EQG in Q4.
exact (proj1 (Forall_forall _ _) Q4 (bl, el) ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)). }
destruct Hbl as (ib & Hib & Ebl).
eapply evt_cut; [apply (qdrain_ret_app_spec (Z_to_bv 64 0x4a080) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2056) lo pre (ql Σ) bl el Hne QGr' QT WF');
try (rewrite qbytes_app in HBYg'; exact HBYg');
try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
[exact LK | exact QM | exact STd | exact MI]|].
intros ms (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
rewrite Esp in MU2, ST2.
apply (xr_tail [(bl, bl + 8)] [(24, ib)] u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2); try assumption.
+ intros c i [E|[]]. injection E as <- <-. split; [reflexivity | exact Hib].
+ constructor; [|constructor]. exists 24, ib. split; [left; reflexivity|]. cbn [fst snd]. rewrite Ebl. change (ClassSize 24) with 8192. lia.
+ eapply munch_weaken; [|exact MU2]. unfold W_D, i_q_cmutex, i_q_global, INST, g_instance. cbn [app]. solve_sub_fp.
+ rewrite EQG. exact QG2.
Qed.

End XRun.

Definition dfinal (F : bvmap 5 word) (fc : bv 32) (Σ : rtsA) (PMc : Model -> Prop) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (m : mem) :
config -> Prop :=
fun cf => exists Σ' : rtsA,
ASTA RTA Σ' PMc (dpost F fc Σ' gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp (live Σ) (frames Σ) m) cf
/\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ rtA_pois Σ' = rtA_pois Σ.

Theorem drain_xfer : forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11
t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
fdfs_only PMc -> mat_stable PMc ->
ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < X0fy.qbytes (ql Σ) ->
qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6 ->
stk asegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
mem_inv asegs m ->
X0id.qbytes (qg Σ ++ ql Σ) <= 0x10000000 ->
cps asegs (ASTA RTA Σ PMc (eq (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
(dfinal F fc Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
intros Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI HBYg.
intros TT cf Hc0 Hk.
pose proof (xfer_evt Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
w0 w1 w2 w3 w4 w5 s6 HA HW HC HBY FR ST HLO HLO2 HSP MI HBYg) as W1.
lazymatch type of W1 with evt asegs _ ?X => assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc0).
intros c1 Hc1. apply Hk. exists (set_q Σ [] (qg Σ ++ ql Σ)).
split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. eapply AST_conseq; [exact Hc1| |].
- intros ms P. exact P.
- intros mo (HM & HP). split; [|exact HP]. cbn [ARTM RTA]. apply (artm_eq Σ); [reflexivity | reflexivity | reflexivity | exact HM].
Qed.
End RL_drain_xfer.
Export RL_drain_xfer.

Module RL_drain_rhead.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0hs X0id X0i8 X0i7 X0hy X0ib X0ic X0fy X0fg X0da X0g4 X0d8 X0fq X0e4 X0e8 X0d9 X0e5 X0e6 X0df X0ci X0cr X0cp X0cv X0cn X0c8.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer.

Definition bidx (SB b : Z) : nat := Z.to_nat ((b - SB - 24 * 2 ^ 32) / 8192).
Definition bslots (SB : Z) (bs : list batch) : list (Z * nat) := map (fun b => (24, bidx SB (fst b))) bs.

Lemma bidx_abeg : forall SB i, bidx SB (p_abeg SB 24 i) = i.
Proof.
intros SB i. unfold bidx, p_abeg. change (ClassSize 24) with 8192.
replace (SB + 24 * 2 ^ 32 + Z.of_nat i * 8192 - SB - 24 * 2 ^ 32) with (Z.of_nat i * 8192) by lia.
rewrite Z.div_mul by lia. apply Nat2Z.id.
Qed.

Lemma bslots_ok : forall Σ bs, Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) bs ->
forall c i, In (c, i) (bslots (l_SB (lay Σ)) bs) -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch.
Proof.
intros Σ bs HB c i Hin. unfold bslots in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
destruct (proj1 (Forall_forall _ _) HB b Hb) as (j & Hj & Eb). rewrite Eb, bidx_abeg. split; [reflexivity | exact Hj].
Qed.

Lemma bslots_cover : forall Σ bs, Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) bs ->
Forall (fun iv => exists c i, In (c, i) (bslots (l_SB (lay Σ)) bs) /\ p_abeg (l_SB (lay Σ)) c i <= fst iv /\ snd iv <= p_abeg (l_SB (lay Σ)) c i + ClassSize c)
(bivs bs).
Proof.
intros Σ bs HB. apply Forall_forall. intros iv Hiv. unfold bivs in Hiv. apply in_map_iff in Hiv as (b & <- & Hb).
destruct (proj1 (Forall_forall _ _) HB b Hb) as (j & Hj & Eb). exists 24, j. split.
- unfold bslots. apply in_map_iff. exists b. split; [rewrite Eb, bidx_abeg; reflexivity | exact Hb].
- cbn [fst snd]. rewrite Eb. change (ClassSize 24) with 8192. lia.
Qed.

Section RRun.
Variables (Σ : rtsA) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word).
Hypothesis HA : ARTc Σ m.
Hypothesis HW : rt_wfx Σ.
Hypothesis HC : rt_count Σ.
Hypothesis HBY : 0x100000 < X0fy.qbytes (ql Σ).
Hypothesis FR : qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714)
w0 w1 w2 w3 w4 w5 s6.
Hypothesis ST : stk asegs m lo (usp + -2208).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x4000 <= usp + -2208.
Hypothesis HSP : usp <= 2 ^ 47.
Hypothesis MI : mem_inv asegs m.
Hypothesis HBYr : 0x10000000 < X0id.qbytes (qg Σ ++ ql Σ).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation G := (qg Σ ++ ql Σ).

Definition rh_entry (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x47bc0) (Z_to_bv 64 (usp + -2288)) gp (Z_to_bv 64 tpA) t0' t1' t2' s0' s1' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (usp + -2288)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) a4' a5' a6' a7' s2' s3' s4' s5
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 qdorec_entry) fc None m3 (seg_rom asegs).

Definition rh_post : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word) (m3 : mem),
ms = rh_entry t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' m3
/\ ARTc (set_q Σ [] (rec_r G QMIN)) m3 /\ qcache_rep m3 (usp + -2288) (rec_x G QMIN)
/\ qrec_frame m3 (usp + -2288) (Z_to_bv 64 0x4a080) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4
/\ qput_frame m3 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6
/\ stk asegs m3 lo (usp + -2288) /\ mem_inv asegs m3 /\ wmono asegs m m3 /\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m3.

Lemma rr_qg : exists pre bl el, qg Σ = pre ++ [(bl, el)].
Proof using HW HBYr.
destruct (qg Σ) as [|b0 rest] eqn:E.
- exfalso. pose proof HW as (_ & _ & _ & _ & (Q1 & _) & _). cbn [app] in HBYr. rewrite <- qbytes_eq in HBYr.
unfold QMAX_L in Q1. lia.
- destruct (exists_last (l := b0 :: rest) ltac:(discriminate)) as (pre & (bl & el) & E2). exists pre, bl, el. exact E2.
Qed.

Definition W_RH (T usp bl : Z) (bs : list batch) : list ivl :=
[(i_q_cmutex, i_q_cmutex + 4); (i_q_global, i_q_global + 32); (T + 80, T + 112); (bl, bl + 8); (usp - 2304, usp - 2208)] ++ bivs bs.

Lemma rr_cert : forall bl, In bl (map fst G) ->
Forall (dzone Σ (bslots SB G) [] [] (TZ_X T) IZ_Q [] lo (usp + -2128)) (W_RH T usp bl G).
Proof using HW HLO2.
intros bl Hbl. pose proof HW as (_ & _ & _ & _ & (_ & _ & Q4 & _) & _).
assert (Q4' : Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg SB 24 i) G)
by (apply (Permutation_Forall (Permutation_app_comm (ql Σ) (qg Σ))); exact Q4).
unfold W_RH. apply Forall_app. split.
- constructor; [left; exists (i_q_cmutex, i_q_cmutex + 4); split; [left; reflexivity | cbn; lia]|].
constructor; [left; exists (i_q_global, i_q_global + 32); split; [right; left; reflexivity | cbn; lia]|].
constructor; [right; left; exists (T + 80, T + 112); split; [left; reflexivity | cbn; lia]|].
constructor.
{ right; right; left. apply in_map_iff in Hbl as (b & E & Hb). destruct (proj1 (Forall_forall _ _) Q4' b Hb) as (j & Hj & Eb).
exists 24, j. split; [unfold bslots; apply in_map_iff; exists b; split; [rewrite Eb, bidx_abeg; reflexivity | exact Hb]|].
cbn [fst snd]. rewrite <- E, Eb. change (ClassSize 24) with 8192. lia. }
constructor; [do 9 right; cbn; lia | constructor].
- apply Forall_forall. intros iv Hiv. right; right; left. exact (proj1 (Forall_forall _ _) (bslots_cover Σ G Q4') iv Hiv).
Qed.

Theorem rr_evt : evt asegs rh_post (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp).
Proof using HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr.
pose proof (xr_geo Σ HW) as (HG & X1 & X2 & X3 & X4 & X6 & X7 & X8 & X9). unfold SHB in X8.
pose proof (xq_cells Σ m HA) as (QT & QGr & LK & QM).
apply (proj1 (rwc_app asegs m q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661)] [C8 (Z_to_bv 64 0x100000)])) in QM.
destruct QM as (QM & _).
pose proof (qwf_of_wfx Σ HW) as WF.
assert (Hne : ql Σ <> []) by (intros E; pose proof HBY as X; rewrite E in X; change (X0fy.qbytes []) with 0 in X; lia).
assert (Esp : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
assert (STd : stk asegs m lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST).
destruct rr_qg as (pre & bl & el & EQG).
assert (Hbl : In bl (map fst G)) by (rewrite EQG; apply in_map_iff; exists (bl, el); split; [reflexivity | apply in_or_app; left; apply in_or_app; right; left; reflexivity]).
eapply evt_cut; [exact (xr_head Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
w0 w1 w2 w3 w4 w5 s6 HA HW HBY FR ST HLO HLO2 HSP MI)|].
intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->). unfold xr_dentry.
pose proof QGr as QGr'. pose proof WF as WF'. pose proof HBYr as HBYr'. rewrite EQG in QGr', WF', HBYr'.
assert (HBY2 : 0x10000000 < X0id.qbytes (pre ++ [(bl, el)]) + X0id.qbytes (ql Σ) < 2 ^ 56).
{ rewrite <- qbytes_app. split; [exact HBYr'|]. pose proof HW as (_ & _ & _ & _ & (Q1 & Q2 & _) & _).
rewrite <- EQG, qbytes_app, <- !qbytes_eq. unfold QMAX_L, QMAX_G in *. lia. }
eapply evt_cut; [apply (qdrain_rec_app_spec (Z_to_bv 64 0x4a080) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m (T + 80) SB (T + 208) (usp + -2056) lo pre (ql Σ) bl el Hne QGr' QT WF' HBY2 LK QM);
try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
[exact STd | exact MI]|].
intros ms (u0 & u1 & u2 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & QG2 & QT2 & LK2 & ST2).
rewrite Esp in MU2, ST2. rewrite <- EQG in QG2.
assert (HBYG : X0id.qbytes G < 2 ^ 56) by (rewrite EQG, qbytes_app; lia).
assert (ST2' : stk asegs m2 lo (bv_unsigned (Z_to_bv 64 (usp + -2208)))) by (rewrite Esp; exact ST2).
eapply evt_mono; [apply (qrec_A_spec_closed (Z_to_bv 64 0x4a080) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) u0 u1 u2
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) v4 v5 v6 v7 s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11
u3 u4 u5 u6 F fc m2 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) QMIN SB lo G QG2 WF HBYG);
try (unfold QMIN; lia); try (clear - X1 X2 X3 X4 X6 X7 X8 X9 HLO HLO2 HSP Esp; rewrite ?Esp; unfold r24, SEGTOP_A in *; lia);
[exact LK2 | exact ST2' | exact MI2]|].
intros ms (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & y3 & y4 & y5 & y6 & m3 & -> & MU3 & WM3 & MI3 & QG3 & TQ3 & LK3 & FR3 & ST3).
rewrite Esp in MU3, ST3, TQ3, FR3. replace (usp + -2208 + -80) with (usp + -2288) in ST3, TQ3, FR3 by lia.
rewrite Esp. replace (usp + -2208 + -80) with (usp + -2288) by lia.
exists y0, y1, y2, z0, z1, z5, z6, z7, z8, z2, z3, z4, y3, y4, y5, y6, m3. split; [reflexivity|].

assert (MU : munch (W_RH T usp bl G) m m3).
{ apply (munch_trans _ m m2 m3).
- eapply munch_weaken; [|exact MU2]. intros x Hx. unfold W_RH in Hx. apply (proj1 (X0i8.outside_app _ _ _)) in Hx. destruct Hx as (Hx & _).
cbn [outside] in Hx |- *. unfold i_q_cmutex, i_q_global, INST, g_instance in *. lia.
- eapply munch_weaken; [|exact MU3]. intros x Hx. unfold W_RH in Hx. apply (proj1 (X0i8.outside_app _ _ _)) in Hx. destruct Hx as (Hx & Hb).
apply (proj2 (X0i8.outside_app _ _ _)). split; [|exact Hb].
cbn [outside] in Hx |- *. unfold i_q_cmutex, i_q_global, INST, g_instance in *. lia. }
assert (WM : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM2 WM3).
pose proof (rr_cert bl Hbl) as CERT. pose proof (xr_TZ Σ) as (TZ1 & TZ2).
pose proof HW as (_ & _ & HV & _ & (_ & _ & Q4 & _) & _ & _ & Hdep & _).
assert (Q4' : Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg SB 24 i) G)
by (apply (Permutation_Forall (Permutation_app_comm (ql Σ) (qg Σ))); exact Q4).
pose proof (bslots_ok Σ G Q4') as HD.
assert (HQ : quar_rep (set_q Σ [] (rec_r G QMIN)) m3).
{ unfold quar_rep. cbn [lay ql qg set_q]. split; [|split; [exact QG3 | exact LK3]].
apply (qcache_rep_frame _ m2 m3 _ _ QT2 MU3 WM3); [|constructor].
apply disjoint_from_app; [cbn [disjoint_from]; unfold qcacheT; unfold SEGTOP_A in *; repeat split; lia|].
apply disjoint_bivs. apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Q4' e He) as (j & Hj & Ej).
pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). pose proof (dk_T Σ HG) as (_ & _ & _ & _ & T5).
pose proof (dk_geo Σ HG) as (_ & _ & _ & _ & _ & G6 & G7 & _). rewrite Ej. unfold qcacheT. change (ClassSize 24) with 8192 in *. lia. }
split; [exact (artc_q Σ m m3 (W_RH T usp bl G) (bslots SB G) (TZ_X T) lo (usp + -2128) [] (rec_r G QMIN) HG HD TZ1 TZ2 HLO CERT HA Hdep MU WM HQ)|].
split; [exact TQ3|]. split; [exact FR3|].
split.
{ unfold qput_frame in *. apply (rw_cells_transport asegs _ m m3 _ _ FR MU WM). cbn [cells_size csize Nat.add Z.of_nat].
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
unfold W_RH. apply disjoint_from_app.
- apply in_map_iff in Hbl as (b & Eb & Hb). destruct (proj1 (Forall_forall _ _) Q4' b Hb) as (j & Hj & Ej).
pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). rewrite <- Eb, Ej.
cbn [disjoint_from]. unfold i_q_cmutex, i_q_global, INST, g_instance. change (ClassSize 24) with 8192 in *. unfold SHB in G1.
repeat split; lia.
- apply disjoint_bivs. apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Q4' e He) as (j & Hj & Ej).
pose proof (dk_slot_in Σ HG 24 j CkBatch ltac:(lia) Hj) as (S1 & S2 & _). rewrite Ej. change (ClassSize 24) with 8192 in *. lia. }
split; [exact ST3|]. split; [exact MI3|]. split; [exact WM|].
exact (client_q Σ m m3 (W_RH T usp bl G) (bslots SB G) (TZ_X T) lo (usp + -2128) HG HD TZ1 HLO ltac:(clear - HLO2; lia) CERT HV MU).
Qed.

End RRun.
End RL_drain_rhead.
Export RL_drain_rhead.

Module RL_dsec_defs.
Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0hb X0j3 X0il X0gp X0id X0i8 X0ib X0hx X0hv X0hm X0fy X0fg X0e5 X0ci.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead.

Section Cuts.
Variables (p : dlp) (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat) (s : secst).
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

Definition ds_loopmem (m : mem) : Prop :=
(exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G)
/\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
/\ drec_frame m C j (T + 208) (usp - 2056) (Z_to_bv 64 0x47bc0) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
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
End RL_dsec_defs.
Export RL_dsec_defs.

Module RL_dsec_runA.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0hb X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0ib X0hx X0hv X0il X0iz X0hw X0gx X0hm X0iw X0iy X0ix X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0db X0dc X0f1 X0ci X0cr X0cp X0cn X0ck X0cs X0d1 X0d3 X0d2 X0cy.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead RL_dsec_defs.

Lemma outside_incl : forall W1 W2 x, (forall iv, In iv W1 -> In iv W2) -> outside W2 x -> outside W1 x.
Proof.
intros W1 W2 x HI H. apply outside_Forall. apply Forall_forall. intros iv Hiv.
exact (proj1 (Forall_forall _ _) (proj1 (outside_Forall W2 x) H) iv (HI iv Hiv)).
Qed.

Section RunA.
Variables (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat)
(s : secst) (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word).
Hypothesis HOK : dl_ok p.
Hypothesis HWP : rt_wfP Σk ((b, skipn i ents) :: rest).
Hypothesis HS : dl_sig p Σk.
Hypothesis Hk : nth_error (sec Σk) k = Some s.
Hypothesis Hq : s_quar s = true.
Hypothesis DM : dl_mem p j Σk rest m.
Hypothesis QB : qbatch m b (qfirst rest) ents.
Hypothesis Hib : nth_error (r_st (pr Σk 24)) ib = Some CkBatch.
Hypothesis Eb : b = p_abeg (l_SB (lay Σk)) 24 ib.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation L := (lay Σk).
#[local] Notation T := (l_T (lay Σk)).
#[local] Notation TCX := (l_TCX (lay Σk)).
#[local] Notation SB := (l_SB (lay Σk)).
#[local] Notation PAB := (l_PAB (lay Σk)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).
#[local] Notation n := (s_n s).
#[local] Notation M := (s_mb s + 6128).
#[local] Notation NS := (length (sec Σk)).

Definition ds_ms : machine_state :=
MS (mkR (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
(Z_to_bv 64 (C - 104)) (Z_to_bv 64 M) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom asegs).

Definition svc_mad : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (mA : mem) (ws : list word) (lst : secst) (muw mudw : word),
ms = MSsvc (sd_M_regs (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' MB MSZ a4' a5' a6' (Z_to_bv 64 1023688)
(Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6')
(dl_F p) (Z_to_bv 64 madv_ecall) (Z_to_bv 64 233) (dl_fc p) None mA (seg_rom asegs)
/\ munch (qcbrec_sec_W T (C - 112) ++ sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) m mA /\ wmono asegs m mA
/\ mem_inv asegs mA
/\ sd_mid (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x47e7c) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1023064) MB MSZ
(needed n + rz_size n) TCX T lo muw mudw mA
/\ sd_K1 MB MSZ PAB 0x4000 (Z.of_nat NS) (Z.of_nat k) (s_mb lst) ws mA
/\ Z.of_nat (length ws) = 0x4000 /\ firstn NS ws = map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)
/\ nth_error (sec Σk) (NS - 1) = Some lst.

Lemma ds_run1 : evt asegs svc_mad ds_ms.
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof (dg_ok Σk HG) as (HT & HSB & TSEP).
pose proof HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
pose proof (dg_consts L m A1) as (IC & MMG & TC & PS & STS & UB). destruct IC as (IC1 & IC2).

pose proof HG as (HL & HR & HSW & HFW).
pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & G2 & G3 & G4 & G5) & GP & GF & GS).
pose proof (nth_error_lt _ _ _ Hk) as Hkl.
assert (Hnres : sec_nres Σk = 0x4000) by (apply SW3; intros E; rewrite E in Hk; destruct k; discriminate).
pose proof (smsz_big n ltac:(lia)) as Hbig.

pose proof A5 as (SC & SPD & (ws & WS & Hwsl & Hwsf) & SPG & SRG & SJK & NMC).
rewrite Hnres in SC, Hwsl.
assert (HIN : firstn NS (map bv_unsigned ws) = map s_mb (sec Σk)).
{ rewrite firstn_map, Hwsf, map_map. apply map_ext_in. intros x Hx. apply unsigned_lit.
pose proof (proj1 (Forall_forall _ _) SW4 x Hx) as ((Y1 & _) & (X1 & _ & X3 & _) & _). pose proof (smsz_pos (s_n x) Y1).
pose proof (dk_geo Σk HG) as (_ & X & _). lia. }

pose proof A4 as (_ & CS). pose proof (CS k s Hk) as X. unfold schunk in X. rewrite Hq in X.
replace (s_mb s + 4096 + 2032) with M in X by lia. replace (s_mb s + 4096 + 2048) with (M + 16) in X by lia.
destruct X as (SHD & WRM & LCH & (b1 & ctx & fid & Hb1 & QH) & STSH & SB1 & SB2 & SB3).
apply (proj1 (rwc_app asegs m _ [C1 (Z_to_bv 8 3); C1 b1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] [C8 ctx; C8 fid])) in QH.
destruct QH as (QH & QH2).
assert (Hb1r : 0 <= bv_unsigned b1 < 256) by (pose proof (bv_unsigned_in_range 8 b1) as X; unfold bv_modulus in X; cbn in X; lia).
rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b1) in QH.

destruct (fl_two_c8 m (T + 2840) ltac:(apply (stk_within m _ _ _ _ STS); [lia | lia | pose proof HT as (X & _); lia])) as (rfw & rfdw & STW).
rewrite <- (Z_to_bv_bv_unsigned rfw), <- (Z_to_bv_bv_unsigned rfdw) in STW.
pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
pose proof (g_grant Σk HG PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (PA1 & PA2 & PA3 & PA4 & PA5).
pose proof (g_apart Σk HG 1 2 _ _ ltac:(lia) eq_refl eq_refl) as AP12. cbn [fst snd] in AP12. unfold apart in AP12.
pose proof (proj1 (Forall_forall _ _) GS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as AMT.
cbn [fst snd] in AMT. unfold apart in GP, AMT.
assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
eapply evt_cut.
{ unfold ds_ms.
apply (qcbrec_sec_spec (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL L) SB PAB 0x4000 (Z.of_nat NS) ws MB MSZ
(needed n + rz_size n) (Z.of_nat k) M n (bv_unsigned b1) TCX T (bv_unsigned rfw) (bv_unsigned rfdw) (C - 104) lo);
rewrite ?RSP.
all: try assumption.
- split; [exact SPG|]. split; [exact SC|]. split; [exact SPD|]. split; [exact WS | exact SHD].
- rewrite Hwsl. clear - PA3 HLk. lia.
- unfold hide, img_hull_lo, img_hull_hi. rewrite Hwsl. clear - PA5. unfold SEGTOP_A in *. lia.
- rewrite Hwsl. clear - Hkl SW1. unfold SEC_MAX in *. lia.
- rewrite Nat2Z.id, HIN. apply in_map. exact (nth_error_In _ _ Hk).
- rewrite Nat2Z.id, HIN. apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (x & <- & Hx). intros Hle.
destruct (In_nth_error _ _ Hx) as (jx & Hjx). destruct (Nat.eq_dec jx k) as [->|Hne].
+ rewrite Hk in Hjx. injection Hjx as <-. lia.
+ pose proof (SW5 jx k x s Hjx Hk Hne) as AX. unfold apart in AX.
pose proof (proj1 (Forall_forall _ _) SW4 x Hx) as ((Y1 & _) & _). pose proof (smsz_pos (s_n x) Y1). clear - AX Hle Hbig H Hn1. lia.
- clear - G3 HLk. lia.
- clear; lia.
- clear - Hbig Hn1. lia.
- unfold hide. clear - GP GG6 GG7. lia.
- clear - Hn1 Hn2. lia.
- apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
exact (proj1 IC1).
- unfold hide. rewrite Hwsl. clear - AP12. lia.
- clear - N5. lia.
- clear - N6. lia. }
intros ms1 P1.
destruct P1 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m1 & -> & MU1 & WM1 & MI1 & K1 & ST1).
destruct K1 as ((PG1 & SC1 & PD1 & WS1 & SHD1) & HD1 & STW1).
rewrite RSP in MU1, ST1.

assert (HTZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_ST T)) by (unfold TZ_ST; repeat constructor; cbn; lia).
assert (HTZd : disjoint_from (TZ_ST T) T 0x30 /\ disjoint_from (TZ_ST T) (T + 48) 16 /\ disjoint_from (TZ_ST T) (T + 0xc60) 1
/\ (forall c', 1 <= c' <= 31 -> disjoint_from (TZ_ST T) (pc_addr T c') 80) /\ disjoint_from (TZ_ST T) (qcacheT T) 32).
{ unfold TZ_ST, pc_addr, qcacheT. cbn [disjoint_from]. split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|].
split; [split; [lia | exact I]|]. split; [intros c' Hc'; split; [lia | exact I] | split; [lia | exact I]]. }
assert (CERT1 : Forall (dzoneP Σk [] [] [k; (NS - 1)%nat] (TZ_ST T) IZ_S [] lo (C - 112)) (qcbrec_sec_W T (C - 112))).
{ unfold qcbrec_sec_W. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; lia].
- right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; lia].
- do 9 right. left. cbn. lia. }
pose proof (da_consts Σk m m1 _ k (TZ_ST T) lo (C - 112) HG HTZ HTZd HLk CERT1 HA MU1 WM1) as CR1.
pose proof (dg_consts L m1 CR1) as (IC1' & MMG1 & TC1 & PS1 & STS1 & UB1).
pose proof (ds_rel L m1 CR1) as REL1.

destruct (nth_error (sec Σk) (NS - 1)) as [lst|] eqn:Hlst; [|apply nth_error_None in Hlst; lia].
pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
pose proof (smsz_big (s_n lst) ltac:(lia)) as Lbig.
pose proof (CS _ lst Hlst) as X. unfold schunk, shdr in X. destruct X as (LSHD & _).
apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 (s_mb lst)); C8 (Z_to_bv 64 (smsz (s_n lst))); C8 (Z_to_bv 64 (needed (s_n lst) + rz_size (s_n lst)))]
[C8 (Z_to_bv 64 (Z.of_nat (NS - 1)))])) in LSHD.
destruct LSHD as (_ & LIDX). cbn [cells_size csize Nat.add Z.of_nat] in LIDX.

pose proof (g_grant Σk HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
pose proof (g_grant Σk HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (Y1 & Y2 & Y3 & Y4 & Y5).
pose proof (g_apart Σk HG 1 3 _ _ ltac:(lia) eq_refl eq_refl) as AP13. pose proof (g_apart Σk HG 2 3 _ _ ltac:(lia) eq_refl eq_refl) as AP23.
cbn [fst snd] in AP13, AP23. unfold apart in AP13, AP23.
pose proof (proj1 (Forall_forall _ _) GS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as AMP.
pose proof (proj1 (Forall_forall _ _) GS (TCX, 0x10000) ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as AMX.
pose proof (proj1 (Forall_forall _ _) LGS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as ALP.
pose proof (proj1 (Forall_forall _ _) LGS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as ALT.
pose proof (proj1 (Forall_forall _ _) LGS (TCX, 0x10000) ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as ALX.
cbn [fst snd] in AMP, AMX, ALP, ALT, ALX. unfold apart in AMP, AMX, ALP, ALT, ALX.
assert (ALM : s_mb lst = MB \/ s_mb lst + 32 <= MB \/ MB + MSZ <= s_mb lst).
{ destruct (Nat.eq_dec (NS - 1) k) as [E|E].
- left. rewrite E in Hlst. rewrite Hk in Hlst. injection Hlst as <-. reflexivity.
- pose proof (SW5 (NS - 1)%nat k lst s Hlst Hk E) as A. unfold apart in A. clear - A Lbig Ln1. lia. }

assert (HWI : nth_error ws k = Some (Z_to_bv 64 MB)).
{ assert (E : nth_error (firstn NS ws) k = nth_error (map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)) k) by (rewrite Hwsf; reflexivity).
rewrite nth_error_firstn, nth_error_map, Hk in E. destruct (Nat.ltb_spec k NS); [exact E | lia]. }
assert (HWL : nth_error ws (NS - 1) = Some (Z_to_bv 64 (s_mb lst))).
{ assert (E : nth_error (firstn NS ws) (NS - 1) = nth_error (map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)) (NS - 1)) by (rewrite Hwsf; reflexivity).
rewrite nth_error_firstn, nth_error_map, Hlst in E. destruct (Nat.ltb_spec (NS - 1) NS); [exact E | lia]. }

destruct (fl_two_c8 m1 (T + 2888) ltac:(apply (stk_within m1 _ _ _ _ STS1); [lia | lia | pose proof HT as (X & _); lia])) as (muw & mudw & MUW).
assert (MB8 : MB mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
assert (MSZ8 : MSZ mod 8 = 0).
{ unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed n + rz_size n + 4095) / 4096) * 512 + 512). lia. }
assert (ESH : shad (MB + MSZ) = shad MB + MSZ / 8) by (apply shad_add8'; assumption).
destruct (stk_CB m1 (shad MB) (MSZ / 8) ltac:(rewrite <- ESH; exact (stk_wmono m m1 _ _ STSH WM1)) ltac:(apply Z.div_pos; lia)) as (shj & SHJ).
assert (LIDX1 : rw_cells asegs m1 (s_mb lst + 24) [C8 (Z_to_bv 64 (Z.of_nat (NS - 1)))]).
{ apply (rw_cells_transport asegs _ m m1 _ _ LIDX MU1 WM1). unfold qcbrec_sec_W. cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
unfold i_sec_mutex, INST, g_instance. clear - LG1 LG3 LG5 ALT HLk N5 Lbig Ln1. unfold img_hull_lo, img_hull_hi, SEGTOP_A in *.
repeat split; try exact I; lia. }
assert (SJ1 : sec_junk m1).
{ destruct SJK as ((bj & jj & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)).
unfold qcbrec_sec_W in MU1. unfold i_sec_sorted, i_sec_bylog, i_gstat_alloc, i_sec_mutex, INST, g_instance in *.
split; [exists bj, jj, w1, w2, w3, w4; apply (rw_cells_transport asegs _ m m1 _ _ J1 MU1 WM1); cbn [disjoint_from cells_size csize Nat.add Z.of_nat];
clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia|].
split; [exists bl; split; [exact Hbl|]; apply (u64arr_transport asegs _ m m1 _ _ J2 MU1 WM1); rewrite Hbl; cbn [disjoint_from Z.of_nat];
clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia|].
exists ga, gm. apply (rw_cells_transport asegs _ m m1 _ _ J3 MU1 WM1); cbn [disjoint_from cells_size csize Nat.add Z.of_nat];
clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia. }
apply (proj1 (rwc_app asegs m1 _ [C8 (Z_to_bv 64 MB); C8 (Z_to_bv 64 MSZ); C8 (Z_to_bv 64 (needed n + rz_size n))]
[C8 (Z_to_bv 64 (Z.of_nat k))])) in SHD1.
destruct SHD1 as (HDA & HDI). cbn [cells_size csize Nat.add Z.of_nat] in HDI.
eapply evt_cut.
{ apply (secdealloc_A1_spec (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) u0 u1 u2 (Z_to_bv 64 C) (Z_to_bv 64 INST) u3 u4 u5 u6 u7
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) u8 u9 u10 u11 (dl_F p) (dl_fc p) m1 MB MSZ (needed n + rz_size n) (Z.of_nat k) PAB 0x4000 (Z.of_nat NS)
(s_mb lst) (Z.of_nat (NS - 1)) TCX T lo ws muw mudw shj); rewrite ?RSP.
all: try assumption.
- split; [exact G2|]. split; [clear - Hbig Hn1; lia|].
unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed n + rz_size n + 4095) / 4096) + 1). lia.
- unfold gobj. clear - G1 G3 G4 G5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - PA1 PA3 PA4 PA5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - Y1 Y3 Y4 Y5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - X1 X3 X4 X5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- clear - LG1 LG3 LG4 LG5 HLk Lbig Ln1. unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold sapart. clear - ALP Lbig Ln1. lia.
- unfold sapart. clear - AMX. lia.
- unfold sapart. clear - AP23. lia.
- unfold sapart. clear - AP12. lia.
- unfold sapart. clear - AP13. lia.
- unfold sapart. clear - ALT Lbig Ln1. lia.
- unfold sapart. clear - ALX Lbig Ln1. lia.
- clear - Hkl SW1 Hwsl. unfold SEC_MAX in *. lia.
- rewrite Nat2Z.id. exact HWI.
- replace (Z.to_nat (Z.of_nat NS - 1)) with (NS - 1)%nat by (clear - Hkl; lia). exact HWL.
- clear - HSB HLk. destruct HSB as (? & _ & ? & _). unfold kHighShadowEnd in *. lia.
- clear - N5. lia.
- clear - N6. lia. }
intros ms2 P2.
destruct P2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & m2 & -> & MU2 & WM2 & MI2 & MID2 & K2).
rewrite RSP in MU2.
apply evt_done. unfold svc_mad.
exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, m2, ws, lst, muw, mudw.
split; [reflexivity|].
split.
{ apply (munch_trans _ m m1 m2).
- apply (munch_weaken (qcbrec_sec_W T (C - 112)) _ m m1); [|exact MU1]. intros x Hx. apply outside_app_inv in Hx. exact (proj1 Hx).
- apply (munch_weaken (sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) _ m1 m2); [|exact MU2]. intros x Hx.
apply outside_app_inv in Hx. exact (proj2 Hx). }
split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact MID2|]. split; [exact K2|].
split; [exact Hwsl|]. split; [exact Hwsf | exact Hlst].
Qed.

Lemma ds_fin : forall (W0 : list ivl) (lst : secst) (ws : list word) (m2 : mem) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw : word),
nth_error (sec Σk) (NS - 1) = Some lst -> Z.of_nat (length ws) = 0x4000 ->
firstn NS ws = map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk) ->
munch (W0 ++ [(s_mb lst + 24, s_mb lst + 32)]) m m2 -> wmono asegs m m2 ->
Forall (dzoneP Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112)) W0 ->
sd_K MB MSZ (needed n + rz_size n) PAB 0x4000 (Z.of_nat NS) (Z.of_nat k) (s_mb lst) T ws muw mudw m2 ->
mem_inv asegs m2 -> uod_frame m2 (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x47e7c) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1023064) ->
stk asegs m2 lo (C - 112 - 48) ->
svc_mun p j b ents i rest Σk k s
(MSsvc (uod_regs (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) v0 v1 v2 MB MSZ v3 v4 v5 v6 v7
(Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) v8 v9 v10 v11)
(dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) (dl_fc p) None m2 (seg_rom asegs)).
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
intros W0 lst ws m2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw Hlst Hwsl Hwsf MU WM CERT0 K2 MI2 UF2 ST2.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof HG as (HL & HR & HSW & HFW).
pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
pose proof (nth_error_lt _ _ _ Hk) as Hkl.
assert (Hnres : sec_nres Σk = 0x4000) by (apply SW3; intros E; rewrite E in Hk; destruct k; discriminate).
pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
pose proof (smsz_big (s_n lst) ltac:(clear - Ln1; lia)) as Lbig.
pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
assert (HTZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_ST T)) by (unfold TZ_ST; repeat constructor; cbn; lia).
assert (HTZd : disjoint_from (TZ_ST T) T 0x30 /\ disjoint_from (TZ_ST T) (T + 48) 16 /\ disjoint_from (TZ_ST T) (T + 0xc60) 1
/\ (forall c', 1 <= c' <= 31 -> disjoint_from (TZ_ST T) (pc_addr T c') 80) /\ disjoint_from (TZ_ST T) (qcacheT T) 32).
{ unfold TZ_ST, pc_addr, qcacheT. cbn [disjoint_from]. split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|].
split; [split; [lia | exact I]|]. split; [intros c' Hc'; split; [lia | exact I] | split; [lia | exact I]]. }
destruct K2 as (SCK & PDK & SJK2 & WSK & LIK & _). rewrite Nat2Z.id in WSK.
set (LC := [(s_mb lst + 24, s_mb lst + 32)]) in *.
assert (HQB : Forall (fun b0 => exists j0, nth_error (r_st (pr Σk 24)) j0 = Some CkBatch /\ fst b0 = p_abeg (l_SB (lay Σk)) 24 j0) (ql Σk ++ qg Σk))
by exact (hqb_of_wfP _ _ HWP).
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
assert (CERT : Forall (dzoneP Σk [] [] [k; (NS - 1)%nat] (TZ_ST T) IZ_S [] lo (C - 112)) (W0 ++ LC)).
{ apply Forall_app. split; [apply (dzoneP_mono_DS _ _ _ [k]); [intros x [E|[]]; left; exact E | exact CERT0]|].
apply Forall_cons; [|apply Forall_nil]. do 7 right. left. exists (NS - 1)%nat, lst. split; [right; left; reflexivity|].
split; [exact Hlst|]. cbn [fst snd]. clear - Lbig Ln1. lia. }

assert (LCS : forall a n0, l_ACEIL L <= a -> disjoint_from LC a n0).
{ intros a n0 Ha. unfold LC. cbn [disjoint_from]. split; [|exact I]. clear - Ha LG3 Lbig Ln1. lia. }
assert (STK_AV : forall a n0, C - 112 <= a -> a + n0 <= USTACK_TOP -> disjoint_from (W0 ++ LC) a n0).
{ intros a n0 H1 H2. apply dsj_app; [|apply LCS; clear - H1 HLk N5; lia].
exact (dp_stack_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk ltac:(clear - N5; lia) W0 CERT0 a n0 H1 H2). }
assert (SLOT_AV : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from (W0 ++ LC) (p_abeg SB 24 j') 8192).
{ intros j' Hj'. pose proof (dp_slot_in Σk HG 24 j' _ ltac:(clear; lia) Hj') as (S1 & S2 & _). change (ClassSize 24) with 8192 in S1, S2 |- *.
apply dsj_app.
- exact (dp_slot_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0 24 j' CkBatch (p_abeg SB 24 j') 8192
ltac:(clear; lia) Hj' ltac:(intros []) ltac:(clear; lia) ltac:(change (ClassSize 24) with 8192; clear; lia)).
- unfold LC. cbn [disjoint_from]. split; [|exact I]. clear - S1 S2 LGP GG7 Lbig Ln1. unfold apart in LGP. lia. }
unfold svc_mun. exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, m2. split; [reflexivity|].
split.
{
apply (ds_artc Σk m m2 (W0 ++ LC) k s lst (TZ_ST T) lo (C - 112) ws HG Hk Hlst HTZ HTZd HLk CERT HA Hdep HQB MU WM).
- rewrite Hnres. exact SCK.
- exact PDK. - exact SJK2. - exact WSK. - rewrite Hnres. exact Hwsl. - exact Hwsf.
- intros Hlt. split; [|exact LIK].
assert (HnIn : ~ In (NS - 1)%nat [k]) by (intros [E|[]]; clear - E Hlt; lia).
pose proof (kw_schunk Σk W0 [k] HG
(dp_shad_app_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0)
(dp_secmap_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0)
(NS - 1)%nat lst Hlst HnIn) as (LA1 & LA2 & LA3 & LA4 & LA5 & LA6).
assert (LSH : forall a n0, 0 <= n0 -> shad (s_mb lst) <= a -> a + n0 <= shad (s_mb lst + smsz (s_n lst)) -> disjoint_from LC a n0).
{ intros a n0 H0 H1 H2. unfold LC. cbn [disjoint_from]. split; [|exact I].
pose proof (dp_shad_rng (s_mb lst) ltac:(lia)). pose proof (dp_shad_rng (s_mb lst + smsz (s_n lst)) ltac:(lia)).
clear - H0 H1 H2 H H3 LG4 Lbig Ln1. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia. }
pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 4096 + 2048) ltac:(lia)) as Q1.
pose proof (fk_map Σk HG _ lst Hlst) as (_ & _ & _ & _ & _ & _ & _ & LRoom & LRu & _).
assert (Hru : 8 <= ru8 (s_n lst) /\ s_n lst <= ru8 (s_n lst) /\ 6144 + ru8 (s_n lst) <= smsz (s_n lst)).
{ split; [|split; [exact LRu | exact LRoom]]. unfold ru8.
assert (X : 1 <= (s_n lst + 7) / 8) by (apply Z.div_le_lower_bound; clear - Ln1; lia). clear - X; lia. }
unfold schunk_avoid_nh. split; [|split; [|split; [|split; [|split]]]].
+ apply dsj_app; [apply (dsj_sub W0 (s_mb lst) 32); [exact LA1 | clear; lia | clear; lia]|]. unfold LC. cbn [disjoint_from]. split; [clear; lia | exact I].
+ apply dsj_app; [exact LA2|]. unfold LC. cbn [disjoint_from]. split; [clear; lia | exact I].
+ apply dsj_app; [exact LA3|]. unfold LC. cbn [disjoint_from]. split; [|exact I]. destruct (s_quar lst); clear; lia.
+ apply dsj_app; [exact LA4|]. apply LSH; [clear; lia | clear; lia|]. change ((4096 + 2048) / 8) with 768. rewrite Z.max_r by (clear; lia).
pose proof (fk_shad_le2 (s_mb lst) 6144 ltac:(clear - LG1; lia) ltac:(clear; lia)) as LX1.
pose proof (dp_shad_mono (s_mb lst + 6144) (s_mb lst + smsz (s_n lst)) ltac:(clear - Hru; lia)) as LX2. change (6144 / 8) with 768 in LX1. clear - LX1 LX2. lia.
+ apply dsj_app; [exact LA5|]. destruct Hru as (U1 & U2 & U3).
pose proof (fk_shad_le2 (s_mb lst + 6144) (ru8 (s_n lst)) ltac:(clear - LG1; lia) ltac:(clear - U1; lia)) as E2.
pose proof (dp_shad_mono (s_mb lst + 6144 + ru8 (s_n lst)) (s_mb lst + smsz (s_n lst)) ltac:(clear - U3; lia)) as E4.
pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 6144) ltac:(clear; lia)) as E5.
assert (E7 : 0 <= ru8 (s_n lst) / 8) by (apply Z.div_pos; clear - U1; lia).
replace (s_mb lst + 4096 + 2048) with (s_mb lst + 6144) by (clear; ring).
apply LSH; [clear; lia | exact E5|].
destruct (s_quar lst); [rewrite fdrun_lenZ by exact E7 | rewrite (fl_ushadow_len (s_n lst)) by (clear - Ln1; lia)]; clear - E2 E4; lia.
+ apply dsj_app; [exact LA6|]. destruct Hru as (U1 & U2 & U3).
pose proof (fk_shad_le2 (s_mb lst + 6144 + ru8 (s_n lst)) (smsz (s_n lst) - 6144 - ru8 (s_n lst)) ltac:(clear - LG1 U1; lia) ltac:(clear - U3; lia)) as E3.
replace (s_mb lst + 6144 + ru8 (s_n lst) + (smsz (s_n lst) - 6144 - ru8 (s_n lst))) with (s_mb lst + smsz (s_n lst)) in E3 by (clear; ring).
pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 6144 + ru8 (s_n lst)) ltac:(clear - U1; lia)) as E6.
assert (E8 : 0 <= (smsz (s_n lst) - 6144 - ru8 (s_n lst)) / 8) by (apply Z.div_pos; clear - U3; lia).
replace (s_mb lst + 4096 + 2048 + ru8 (s_n lst)) with (s_mb lst + 6144 + ru8 (s_n lst)) by (clear; ring).
replace (smsz (s_n lst) - 4096 - 2048 - ru8 (s_n lst)) with (smsz (s_n lst) - 6144 - ru8 (s_n lst)) by (clear; ring).
rewrite Z.max_r by exact E8.
apply LSH; [exact E8 | exact E6 | clear - E3; lia]. }
split; [exact MI2|]. split; [exact UF2|]. split; [exact ST2|].

split.
{ destruct WM0 as (G & WG & HGo). exists G. split; [exact (wmono_out_wmono G _ m m2 WG WM) | exact HGo]. }
split.
{ apply (rt_pres_trans _ _ _ _ m m2 RP). intros a Ha. apply MU.
rewrite <- Elv, <- Efr in Ha.
apply (ds_client Σk W0 k s lst (TZ_ST T) lo (C - 112) HG Hk Hq (nth_error_In _ _ Hlst) HTZ HLk ltac:(lia) CERT0 Hlive).
destruct Ha as [Ha|Ha]; [left; clear - Ha; lia | right; exact Ha]. }
pose proof FR as (FR1 & FR2 & FR3).
split.
{ split; [|split].
- apply (rw_cells_transport asegs _ m m2 _ _ FR1 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia.
- apply (rw_cells_transport asegs _ m m2 _ _ FR2 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia.
- apply (rw_cells_transport asegs _ m m2 _ _ FR3 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia. }
split.
{ apply (qcache_rep_frame _ m m2 C rest QR MU WM); [apply STK_AV; clear - N6; unfold USTACK_TOP; lia|].
apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (SLOT_AV j' Hj'). }
apply (qbatch_frame _ m m2 b (qfirst rest) ents QB MU WM). rewrite Eb. exact (SLOT_AV ib Hib).
Qed.

Definition mad_eff : SyscallEffect :=
mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 (pbeg (shad MB)), Z_to_bv 64 (pend (shad (MB + MSZ)) - pbeg (shad MB)))].

Lemma ds_run2 : forall ms0, svc_mad ms0 -> evt asegs (svc_mun p j b ents i rest Σk k s) (nretA ms0 mad_eff).
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & mA & ws & lst & muw & mudw
& -> & MU1 & WM1 & MI1 & MID & K1 & Hwsl & Hwsf & Hlst).
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof (dg_ok Σk HG) as (HT & HSB & TSEP).
pose proof HG as (HL & HR & HSW & HFW).
pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & G2 & G3 & G4 & G5) & GP & GF & GS).
pose proof (nth_error_lt _ _ _ Hk) as Hkl.
pose proof (smsz_big n ltac:(clear - Hn1; lia)) as Hbig.
pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
pose proof (smsz_big (s_n lst) ltac:(clear - Ln1; lia)) as Lbig.
pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
pose proof (g_grant Σk HG PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (PA1 & PA2 & PA3 & PA4 & PA5).
pose proof (g_grant Σk HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
pose proof (g_grant Σk HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (Y1 & Y2 & Y3 & Y4 & Y5).
pose proof (g_apart Σk HG 1 2 _ _ ltac:(clear; lia) eq_refl eq_refl) as AP12. pose proof (g_apart Σk HG 2 3 _ _ ltac:(clear; lia) eq_refl eq_refl) as AP23.
cbn [fst snd] in AP12, AP23. unfold apart in AP12, AP23.
pose proof (proj1 (Forall_forall _ _) GS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as AMP.
pose proof (proj1 (Forall_forall _ _) GS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as AMT.
pose proof (proj1 (Forall_forall _ _) LGS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as ALT.
cbn [fst snd] in AMP, AMT, ALT. unfold apart in AMP, AMT, ALT, GP.
assert (ALM : s_mb lst = MB \/ s_mb lst + 32 <= MB \/ MB + MSZ <= s_mb lst).
{ destruct (Nat.eq_dec (NS - 1) k) as [E|E].
- left. rewrite E in Hlst. rewrite Hk in Hlst. injection Hlst as <-. reflexivity.
- pose proof (SW5 (NS - 1)%nat k lst s Hlst Hk E) as A. unfold apart in A. clear - A Lbig Ln1. lia. }
assert (MB8 : MB mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(clear; lia) G2); exists 512; reflexivity).
assert (MSZ8 : MSZ mod 8 = 0).
{ unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed n + rz_size n + 4095) / 4096) * 512 + 512). clear; lia. }
assert (ESH : shad (MB + MSZ) = shad MB + MSZ / 8) by (apply shad_add8'; assumption).
assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; clear - N5 N6 N4; lia).
eapply evt_cut.
{ unfold mad_eff.
apply (secdealloc_A2_spec (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' (Z_to_bv 64 C) (Z_to_bv 64 INST) a4' a5' a6'
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p) mA MB MSZ (needed n + rz_size n) (Z.of_nat k) PAB 0x4000 (Z.of_nat NS)
(s_mb lst) TCX T lo ws muw mudw); rewrite ?RSP.
all: try assumption.
- split; [exact G2|]. split; [clear - Hbig Hn1; lia|].
unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed n + rz_size n + 4095) / 4096) + 1). clear; lia.
- unfold gobj. clear - G1 G3 G4 G5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - PA1 PA3 PA4 PA5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - Y1 Y3 Y4 Y5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold gobj. clear - X1 X3 X4 X5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- clear - LG1 LG3 LG4 LG5 HLk Lbig Ln1. unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
- unfold sapart. clear - AP23. lia.
- unfold sapart. clear - AP12. lia.
- unfold sapart. clear - ALT Lbig Ln1. lia.
- clear - Hkl SW1 Hwsl. unfold SEC_MAX in *. lia.
- clear - HSB HLk. destruct HSB as (? & _ & ? & _). unfold kHighShadowEnd in *. lia.
- clear - N5. lia.
- clear - N6. lia. }
intros ms2 P2.
destruct P2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & m2 & -> & MU2 & WM2 & MI2 & UF2 & ST2 & K2).
rewrite RSP in MU2, ST2.
apply evt_done.
set (W0 := qcbrec_sec_W T (C - 112) ++ [(shad MB, shad MB + MSZ / 8); (C - 112 - 96, C - 112); (C - 112 - 32, C - 112);
(i_sec_mutex, i_sec_mutex + 4); (i_sec_nres + 8, i_sec_nres + 16); (i_sec_sorted, i_sec_sorted + 40);
(PAB + 8 * Z.of_nat k, PAB + 8 * Z.of_nat k + 8); (i_gstat_alloc, i_gstat_alloc + 16)] ++ sd_W3 (C - 112) MB MSZ T).
apply (ds_fin W0 lst ws m2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw Hlst Hwsl Hwsf); [| exact (wmono_trans _ _ _ _ WM1 WM2) | | exact K2 | exact MI2 | exact UF2 | exact ST2].
- apply (munch_trans (W0 ++ [(s_mb lst + 24, s_mb lst + 32)]) m mA m2).
+ apply (munch_weaken (qcbrec_sec_W T (C - 112) ++ sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) _ m mA); [|exact MU1]. intros x Hx. refine (outside_incl _ _ x _ Hx).
intros iv Hiv. subst W0. unfold qcbrec_sec_W, sd_W, sd_W1, sd_W3 in *. cbn [app In] in Hiv |- *. clear - Hiv.
repeat (destruct Hiv as [Hiv|Hiv]; [subst iv; repeat (first [left; reflexivity | right]) |]). destruct Hiv.
+ apply (munch_weaken (sd_W3 (C - 112) MB MSZ T) _ mA m2); [|exact MU2]. intros x Hx. refine (outside_incl _ _ x _ Hx).
intros iv Hiv. subst W0. unfold qcbrec_sec_W, sd_W, sd_W1, sd_W3 in *. cbn [app In] in Hiv |- *. clear - Hiv.
repeat (destruct Hiv as [Hiv|Hiv]; [subst iv; repeat (first [left; reflexivity | right]) |]). destruct Hiv.
- unfold W0, qcbrec_sec_W, sd_W3. cbn [app].
repeat apply Forall_cons; try apply Forall_nil.
+ left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; clear; lia].
+ right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; clear; lia].
+ do 9 right. left. cbn. clear - N5; lia.
+ do 8 right. left. exists k, s. split; [left; reflexivity|]. split; [exact Hk|]. cbn [fst snd]. rewrite ESH. clear; lia.
+ do 9 right. left. cbn. clear - N5; lia.
+ do 9 right. left. cbn. clear - N5; lia.
+ left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; clear; lia].
+ left. exists (i_sec_nres + 8, i_sec_nres + 16). split; [right; left; reflexivity | cbn; clear; lia].
+ left. exists (i_sec_sorted, i_sec_sorted + 40). split; [right; right; left; reflexivity | cbn; clear; lia].
+ do 10 right. cbn. clear - Hkl SW1. unfold SEC_MAX in *. lia.
+ left. exists (i_gstat_alloc, i_gstat_alloc + 16). split; [right; right; right; left; reflexivity | cbn; clear; lia].
+
do 8 right. left. exists k, s. split; [left; reflexivity|]. split; [exact Hk|]. cbn [fst snd].
assert (SH0 : 0 <= shad MB) by (unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(clear - G1; lia) ltac:(clear; lia)); lia).
pose proof (pbeg_facts (shad MB) SH0) as (PBF & _).
pose proof (pend_facts (shad (MB + MSZ)) ltac:(rewrite ESH; pose proof (Z.div_pos MSZ 8 ltac:(clear - Hbig Hn1; lia) ltac:(clear; lia)); lia)) as (PEF & _).
clear - PBF PEF; lia.
+ do 9 right. left. cbn. clear - N5; lia.
+ right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; clear; lia].
Qed.

End RunA.
End RL_dsec_runA.
Export RL_dsec_runA.

Module RL_dsec_ret.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0hb X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0ib X0hx X0hv X0il X0hm X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0ci X0cr X0cp X0cn X0ck X0d4 X0cz.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead RL_dsec_defs RL_dsec_runA.

Lemma ds_client_map : forall Σ k s z a, geo_ok Σ -> live_wf Σ -> nth_error (sec Σ) k = Some s -> s_quar s = true ->
l_ACEIL (lay Σ) <= z -> aclient (live Σ) (frames Σ) z a ->
~ (s_mb s <= a < s_mb s + smsz (s_n s)) /\ (z <= a \/ a < l_ACEIL (lay Σ)).
Proof.
intros Σ k s z a HG Hlive Hk Hq Hz Ha.
pose proof (an_map Σ k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & SW5 & _).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & _ & _ & AF & _). unfold apart in AF.
destruct Ha as [Hs|[Hcs|[Hl|[Hf|Hfs]]]].
- split; [clear - Hs Hz M2; lia | left; lia].
- destruct Hcs as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; split; [clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia |
clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia | clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia].
- destruct Hl as (p & n & Hin & Hx). destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(t & Ht & Htq & Htn & Ep)].
+ pose proof (dk_slot_in Σ HG c' i' _ Hc' Hn) as (S1 & S2 & _).
assert (Hfit : rz_size n + n <= ClassSize c' /\ 0 <= n).
{ pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
pose proof (fl_rz_facts n) as (R1 & R2). subst p. unfold p_ubeg in Hx.
split; [clear - Hx S1 S2 G7 M5 Hfit R1 R2; lia | right; clear - Hx S1 S2 G7 G4 Hfit R1 R2; lia].
+ subst p. unfold s_ubeg in Hx. rewrite <- Htn in Hx.
destruct (In_nth_error _ _ Ht) as (jt & Hjt).
pose proof (dk_map Σ HG _ t Hjt) as (T1 & T2 & _ & _ & _ & _ & _ & T8 & T9).
pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
destruct (Nat.eq_dec jt k) as [->|Hne].
* rewrite Hk in Hjt. injection Hjt as <-. rewrite Hq in Htq. discriminate.
* pose proof (T9 k s Hk (fun E => Hne (eq_sym E))) as A. unfold apart in A.
split; [clear - Hx A Tbig Tn1; lia | right; clear - Hx T2 Tbig Tn1; lia].
- destruct Hf as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
split; [clear - Hx Y1 Y2 Y3 AF; lia | right; clear - Hx Y2 Y3 Q3; lia].
- destruct Hfs as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
pose proof (dk_geo Σ HG) as (Z1 & Z2 & _).
pose proof (dk_shad_rng f ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X1. pose proof (dk_shad_rng (f + fs_size k0) ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X2.
split; [clear - Hx X1 X2 M3; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia | right; clear - Hx X2 G1; lia].
Qed.

Section Ret.
Variables (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat)
(s : secst).
Hypothesis HOK : dl_ok p.
Hypothesis HWP : rt_wfP Σk ((b, skipn i ents) :: rest).
Hypothesis HS : dl_sig p Σk.
Hypothesis Hk : nth_error (sec Σk) k = Some s.
Hypothesis Hq : s_quar s = true.
Hypothesis Hib : nth_error (r_st (pr Σk 24)) ib = Some CkBatch.
Hypothesis Eb : b = p_abeg (l_SB (lay Σk)) 24 ib.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation L := (lay Σk).
#[local] Notation SB := (l_SB (lay Σk)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).

Definition mun_eff : SyscallEffect := mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 (s_mb s), Z_to_bv 64 (smsz (s_n s)))] [] [].

Lemma ds_ret : forall ms0, svc_mun p j b ents i rest Σk k s ms0 -> evt asegs (dl_N p j b ents i rest (recs Σk k)) (nretA ms0 mun_eff).
Proof using HOK HWP HS Hk Hq Hib Eb.
intros ms0 (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & HA' & MI' & UF' & ST' & LM').
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (an_map Σk k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; clear - N5 N6 N4; lia).
pose proof (dg_consts L m' (proj1 HA')) as (_ & MMG' & _).
eapply evt_mono.
{ unfold mun_eff.
apply (uod_B_spec (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' a2' a3' a4' a5' a6'
(Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p) m' (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1023064)
MB MSZ lo); rewrite ?RSP.
- exact M1. - exact M7. - clear - M2 HLk; lia.
- unfold hide, img_hull_lo, img_hull_hi. clear - M4; unfold SEGTOP_A in *; lia.
- exact UF'. - exact MMG'. - exact ST'.
- clear - HLk G1 G8 G4. unfold kHighShadowEnd, K_HIGH_SHADOW_hi, SHB in *. lia.
- clear - N5; lia. - clear - N6; lia. - exact MI'. }
intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m'' & -> & MU & WB & MI'' & ST'' & _).
rewrite RSP in MU, ST''.
pose proof LM' as ((G & WG & HGo) & RP & FR & QR & QB).

assert (CLI : forall a, aclient (live Σ0) (frames Σ0) (C + 32) a -> outside [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a).
{ intros a Ha. rewrite <- Elv, <- Efr in Ha.
destruct (ds_client_map Σk k s (C + 32) a HG Hlive Hk Hq ltac:(clear - HLk N5; lia) Ha) as (X1 & X2).
cbn [outside]. split; [exact X1|]. split; [|exact I]. clear - X2 HLk N5. lia. }
assert (STA : forall a n0, C - 112 <= a -> 0 <= n0 -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a n0).
{ intros a n0 H1 H2. cbn [disjoint_from]. clear - H1 H2 M2 HLk N5. split; [lia | split; [lia | exact I]]. }
assert (SLA : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] (p_abeg SB 24 j') 8192).
{ intros j' Hj'. pose proof (dk_slot_in Σk HG 24 j' _ ltac:(clear; lia) Hj') as (S1 & S2 & _). change (ClassSize 24) with 8192 in S1, S2.
cbn [disjoint_from]. clear - S1 S2 M5 G7 G4 HLk N5. split; [lia | split; [lia | exact I]]. }
exists (Z_to_bv 64 0x47e7c), y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m''.
split; [rewrite ret_pc_even; [reflexivity | clear; lia | reflexivity]|].
split.
-
split; [exact (ds_art_nw Σk k s lo (C - 112) HG Hk HLk ltac:(clear - N5; lia) ltac:(clear - N6; lia) Hdep HQB m' m'' HA' MU)|].
split; [exact MI''|]. split; [exact ST''|].
split.
{ exists ((MB, MB + MSZ) :: G). split.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2). apply (WB x); [clear - Ho1; lia | exact (WG x Hx Ho2)].
- apply Forall_cons; [|exact HGo]. cbn [fst snd]. intros a Ha. split.
+ intros Hc. rewrite <- Elv, <- Efr in Hc.
destruct (ds_client_map Σk k s (C + 32) a HG Hlive Hk Hq ltac:(clear - HLk N5; lia) Hc) as (X1 & _). exact (X1 Ha).
+ clear - Ha M2 HLk. lia. }
split; [exact (rt_pres_trans _ _ _ _ m' m'' RP (fun a Ha => MU a (CLI _ Ha)))|].
split.
{ pose proof FR as (FR1 & FR2 & FR3). split; [|split].
- apply (rwc_nw _ m' m'' _ _ FR1 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
- apply (rwc_nw _ m' m'' _ _ FR2 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
- apply (rwc_nw _ m' m'' _ _ FR3 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia. }
apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
apply (proj2 (qcache_rep_iff _ _ _)). split.
+ apply (rwc_nw _ m' m'' _ _ QH MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
+ apply (qchain_nw _ m' m'' _ QC MU). apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (SLA j' Hj').
- apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (B1 & (ws & U & Hl & Hf) & Hn).
apply (proj2 (qbatch_iff _ _ _ _)). split; [|split; [|exact Hn]].
+ apply (rwc_nw _ m' m'' _ _ B1 MU). cbn [cells_size csize Nat.add Z.of_nat]. rewrite Eb.
apply (dsj_sub _ (p_abeg SB 24 ib) 8192); [exact (SLA ib Hib) | clear; lia | clear; lia].
+ exists ws. split; [|split; [exact Hl | exact Hf]]. apply (u64_nw _ m' m'' _ _ U MU). rewrite Hl. rewrite Eb.
apply (dsj_sub _ (p_abeg SB 24 ib) 8192); [exact (SLA ib Hib) | clear; lia | clear; lia].
Qed.

End Ret.
End RL_dsec_ret.
Export RL_dsec_ret.

Module RL_dsec.
Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0ib X0hx X0hv X0hm X0gx X0iy X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0g3 X0ci X0cr X0cp X0cn X0ck X0d8 X0db X0ew X0cz.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead RL_dsec_defs RL_dsec_runA RL_dsec_ret.

Lemma ds_FOP_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
forall l l', Permutation l l' -> ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
intros X R Hs l l' H. induction H as [|x l l' Hp IH|x y l|l l' l'' _ IH1 _ IH2]; intros HF.
- constructor.
- inversion HF as [|? ? Hx Hl]; subst. constructor; [|exact (IH Hl)].
apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hx). exact (Permutation_in _ (Permutation_sym Hp) Hz).
- inversion HF as [|? ? Hy Hl]; subst. inversion Hl as [|? ? Hx Hl']; subst.
inversion Hy as [|? ? Hyx Hyl]; subst.
constructor; [constructor; [exact (Hs _ _ Hyx)| exact Hx]|]. constructor; [exact Hyl| exact Hl'].
- exact (IH2 (IH1 HF)).
Qed.

Lemma ds_FOP_app_cross : forall {X} (R : X -> X -> Prop) l1 l2, ForallOrdPairs R (l1 ++ l2) ->
forall x y, In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|q l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
cbn [app] in H. inversion H as [|? ? Hp Hl]; subst. destruct Hx as [<-|Hx].
- apply (proj1 (Forall_forall _ _) Hp). apply in_or_app. right. exact Hy.
- exact (IH l2 Hl x y Hx Hy).
Qed.

Lemma ds_filter_all_true : forall {X} (f : X -> bool) (l : list X), (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
intros X f l. induction l as [|x l IH]; intros H; [reflexivity|]. cbn [List.filter]. rewrite (H x (or_introl eq_refl)).
f_equal. apply IH. intros y Hy. exact (H y (or_intror Hy)).
Qed.

Lemma ds_perm_filter : forall {X} (f : X -> bool) (l l' : list X), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
intros X f l l' H. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2].
- constructor.
- cbn [List.filter]. destruct (f x); [apply perm_skip; exact IH | exact IH].
- cbn [List.filter]. destruct (f x), (f y); try apply perm_swap; apply Permutation_refl.
- exact (Permutation_trans IH1 IH2).
Qed.

Lemma ds_FOP_filter : forall {X} (R : X -> X -> Prop) (f : X -> bool) (l : list X), ForallOrdPairs R l -> ForallOrdPairs R (List.filter f l).
Proof.
intros X R f l H. induction H as [|x l Hx Hl IH]; [constructor|]. cbn [List.filter]. destruct (f x); [|exact IH].
constructor; [|exact IH]. apply Forall_forall. intros y Hy. apply List.filter_In in Hy as [Hy _].
exact (proj1 (Forall_forall _ _) Hx y Hy).
Qed.

Lemma ds_maps0_pos : forall L, layout_ok L -> Forall (fun e => 0 < bv_unsigned (snd e)) (l_maps0 L).
Proof.
intros L HL. unfold layout_ok in HL.
destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & HP) & _).
exact HP.
Qed.

Lemma ds_filter_map : forall {X Y} (f : Y -> bool) (g : X -> Y) (l : list X),
List.filter f (map g l) = map g (List.filter (fun x => f (g x)) l).
Proof. intros X Y f g l. induction l as [|x l IH]; [reflexivity|]. cbn [map List.filter]. destruct (f (g x)); cbn [map]; rewrite IH; reflexivity. Qed.

Lemma ds_lit_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
intros x y Hx Hy E. rewrite <- (unsigned_lit x Hx), <- (unsigned_lit y Hy). rewrite E. reflexivity.
Qed.

Theorem ds_perm : forall Σ k s mo, nth_error (sec Σ) k = Some s -> geo_ok Σ -> ARTM_A Σ mo ->
Permutation (rt_maps (recs Σ k)) (map_remove (rt_maps Σ) (Z_to_bv 64 (s_mb s))).
Proof.
intros Σ k s mo Hk HG HA.
pose proof (ds_maps0_pos _ (proj1 HG)) as HPOS.
pose proof HA as (Hperm & _ & _ & _ & (_ & _ & Hsep0 & _)).
pose proof (ds_FOP_filter iv_apart vpos _ Hsep0) as Hsep.
pose proof (dk_map Σ HG k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & M9).
pose proof (dk_geo Σ HG) as (_ & G2 & _).
pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
pose proof (nth_error_lt _ _ _ Hk) as Hkl.
unfold rt_maps, map_remove. cbn [recs set_sec sec lay]. rewrite filter_app.
assert (E0 : List.filter (fun q => negb (bv_eqb (fst q) (Z_to_bv 64 (s_mb s)))) (l_maps0 (lay Σ)) = l_maps0 (lay Σ)).
{ apply ds_filter_all_true. intros e He. apply negb_true_iff. destruct (bv_eqb (fst e) (Z_to_bv 64 (s_mb s))) eqn:Eb; [|reflexivity].
exfalso. apply bv_eqb_eq in Eb.
assert (HsepR : ForallOrdPairs iv_apart (map secmap (rev (sec Σ)) ++ l_maps0 (lay Σ)))
by exact (ds_FOP_perm iv_apart (fun x y H => ltac:(unfold iv_apart in *; clear - H; lia)) _ _ Hperm Hsep).
pose proof (ds_FOP_app_cross _ _ _ HsepR (secmap s) e ltac:(apply in_map; apply (proj1 (in_rev _ _)); exact (nth_error_In _ _ Hk)) He) as D.
pose proof (proj1 (Forall_forall _ _) HPOS e He) as Pe.
unfold iv_apart, secmap in D. cbn [fst snd] in D. rewrite Eb in D.
rewrite !unsigned_lit in D by (clear - M1 M2 M8 G2; lia). cbv beta in Pe. clear - D Pe M8. lia. }
rewrite E0. apply Permutation_app_tail.
rewrite ds_filter_map. apply Permutation_map.
eapply perm_trans; [apply Permutation_sym, Permutation_rev|]. eapply perm_trans; [|apply ds_perm_filter, Permutation_rev].
eapply perm_trans; [|apply ds_perm_filter, Permutation_sym, (swap_remove_perm k (sec Σ) s Hk)].
cbn [List.filter]. unfold secmap at 1. cbn [fst]. rewrite bv_eqb_refl. cbn [negb].
rewrite ds_filter_all_true; [apply Permutation_refl|].
intros t Ht. apply negb_true_iff. unfold secmap. cbn [fst].
destruct (bv_eqb (Z_to_bv 64 (s_mb t)) (Z_to_bv 64 (s_mb s))) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_eq in Eb.
destruct (swap_remove_other k (sec Σ) t Hkl Ht) as (jt & Hne & Hjt).
pose proof (dk_map Σ HG jt t Hjt) as (T1 & T2 & _ & _ & _ & _ & _ & T8 & _).
pose proof (M9 jt t Hjt Hne) as A.
apply ds_lit_inj in Eb; [|lia | lia]. lia.
Qed.

Lemma ds_smsz_le : forall n, 64512 < n <= 0x8000000 -> smsz n <= 2 ^ 28.
Proof.
intros n Hn. unfold smsz, pg_up, needed, rounded. rewrite (rz_size_big n) by lia. rewrite !Z.max_l by lia.
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
pose proof (Z.div_mod (8 * ((n + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
pose proof (Z.mod_pos_bound (8 * ((n + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma ds_mad_geo : forall Σ k s, geo_ok Σ -> nth_error (sec Σ) k = Some s ->
pbeg (shad (s_mb s)) mod 4096 = 0 /\ pend (shad (s_mb s + smsz (s_n s))) mod 4096 = 0
/\ pbeg (shad (s_mb s)) < pend (shad (s_mb s + smsz (s_n s)))
/\ (K_LOW_SHADOW_lo <= pbeg (shad (s_mb s)) /\ pend (shad (s_mb s + smsz (s_n s))) <= K_LOW_SHADOW_hi
\/ K_HIGH_SHADOW_lo <= pbeg (shad (s_mb s)) /\ pend (shad (s_mb s + smsz (s_n s))) <= K_HIGH_SHADOW_hi)
/\ (forall p : word, pbeg (shad (s_mb s)) <= bv_unsigned p -> bv_unsigned p + 4096 <= pend (shad (s_mb s + smsz (s_n s))) ->
page_allowedb (rtA_allow Σ) p = true).
Proof.
intros Σ k s HG Hk.
pose proof (dk_map Σ HG k s Hk) as (M1 & M2 & M3 & M4 & _ & _ & _ & M8 & _).
pose proof (dk_geo Σ HG) as (_ & G2 & _).
pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _ & SW6).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & GA & _) & _).
pose proof (proj1 (Forall_forall _ _) SW6 s (nth_error_In _ _ Hk)) as HAW.
pose proof (ds_smsz_le (s_n s) ltac:(lia)) as Hsz.
pose proof (smsz_big (s_n s) ltac:(lia)) as Hbig.
assert (MSZ4 : smsz (s_n s) mod 4096 = 0).
{ unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) + 1). lia. }
assert (MB8 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) GA); exists 512; reflexivity).
assert (MSZ8 : smsz (s_n s) mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) MSZ4); exists 512; reflexivity).
assert (ESE : shad (s_mb s + smsz (s_n s)) = shad (s_mb s) + smsz (s_n s) / 8) by (apply shad_add8'; assumption).
set (MB := s_mb s) in *. set (MSZ := smsz (s_n s)) in *.
assert (SH0 : 0 <= shad MB) by (unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(lia) ltac:(lia)); lia).
assert (Q8lo : 8192 <= MSZ / 8) by (apply Z.div_le_lower_bound; lia).
pose proof (pbeg_facts (shad MB) SH0) as (PBR & PBA).
pose proof (pend_facts (shad (MB + MSZ)) ltac:(rewrite ESE; lia)) as (PER & PEA).
rewrite ESE in PER.
split; [exact PBA|]. split; [exact PEA|]. split; [rewrite ESE; lia|].
split.
{ rewrite ESE. clear - M1 M2 M4 G2 PBR PER ESE MB8 MSZ8. unfold shad in *. pose proof (Z.div_mod MB 8 ltac:(lia)) as D1.
pose proof (Z.div_mod (MB + MSZ) 8 ltac:(lia)) as D2. rewrite MB8 in D1. rewrite Z.add_mod, MB8, MSZ8 in D2 by lia. cbn in D2.
unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. destruct M4 as [X|X]; [left | right]; lia. }
intros p' H1 H2. rewrite ESE in H2. unfold page_allowedb. apply existsb_exists. exists (pg_dn (shad MB), pg_up (shad (MB + MSZ))).
split; [unfold rtA_allow; apply in_or_app; left; exact HAW|]. cbn [fst snd]. unfold page_size.
pose proof (pg_dn_facts (shad MB) ltac:(unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(lia) ltac:(lia)); lia)) as (D1 & _).
pose proof (pg_up_facts (shad (MB + MSZ)) ltac:(unfold shad, SHB; pose proof (Z.div_pos (MB + MSZ) 8 ltac:(lia) ltac:(lia)); lia)) as (U1 & _).
apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Section ISec.
Variable p : dlp.
Hypothesis MN : munmap_node.
Hypothesis AN : madvise_node.
Hypothesis HOK : dl_ok p.
#[local] Notation PMc := (dl_PMc p).

Lemma ds_mun : forall j Σk b ib ents i rest k s, rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib -> nth_error (sec Σk) k = Some s -> s_quar s = true ->
cps asegs (ASTA RTA Σk PMc (svc_mun p j b ents i rest Σk k s)) (ASTA RTA (recs Σk k) PMc (dl_N p j b ents i rest (recs Σk k))).
Proof using MN HOK.
intros j Σk b ib ents i rest k s HWP HS Hib Eb Hk Hq.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & HR & _ & HSW & _ & _ & HB & _).
pose proof HB as (B1 & B2 & B3 & B4 & B5).
pose proof (dk_map Σk HG k s Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof HSW as (_ & _ & _ & SW4 & _). pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & (G1 & G2 & _) & _).
eapply cps_seq.
- intros T cf Hcf HK. pose proof Hcf as (_ & _ & (HAM & _) & _). cbn [ARTM RTA] in HAM.
apply (MN Σk (recs Σk k) PMc (svc_mun p j b ents i rest Σk k s) (fun ms => exists ms0, svc_mun p j b ents i rest Σk k s ms0 /\ ms = nretA ms0 (mun_eff s))
(s_mb s) (smsz (s_n s)) FDO MST eq_refl eq_refl); [| | | exact HL | clear - B1 B3; lia | exact B4 | exact M8 | | clear - M1; lia | exact G2 | exact M2 | | exact Hcf | exact HK].
+ change (In (secmap s) (map secmap (rev (sec Σk)))). apply in_map. apply (proj1 (in_rev _ _)). exact (nth_error_In _ _ Hk).
+ exact (ds_perm Σk k s (cfg_model cf) Hk HG HAM).
+ pose proof (secsum_recs Σk k s Hk) as E. unfold rt_eager. change (secsum Σk) with (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec Σk)) in E.
change (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec (recs Σk k))) with (secsum (recs Σk k)).
change (sum_cls (fun c => r_muser (pr (recs Σk k) c) + r_mfa (pr (recs Σk k) c)) 31) with (sum_cls (fun c => r_muser (pr Σk c) + r_mfa (pr Σk c)) 31).
change (sec_nres (recs Σk k)) with (sec_nres Σk). rewrite E. clear; lia.
+ unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) + 1). clear; lia.
+ intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & _).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists (MSsvc (uod_regs (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (dl_usp p - 2288 - 112))
(dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s)) a2' a3' a4' a5' a6' (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37))
(Z_to_bv 64 (Z.of_nat (length ents))) (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16))
(Z_to_bv 64 (16 + Z.of_nat i)) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6') (dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215)
(dl_fc p) None m' (seg_rom asegs)). split; [exact Hms | reflexivity].
- apply (dl_evt (recs Σk k) PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
exact (ds_ret p j b ib ents i rest Σk k s HOK HWP HS Hk Hq Hib Eb ms0 Hms0).
Qed.

Theorem item_sec_ok : item_sec_stmt p.
Proof using MN AN HOK.
intros j Σk b ib ents i rest k s Hi HWP HS Hib Eb Hk Hq Hent.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
assert (Esk : skipn i ents = (s_mb s + 6128, s_n s) :: skipn (S i) ents)
by (rewrite (skipn_nth_cons ents i (0, 0) Hi), Hent; reflexivity).
assert (HWPc : rt_wfP Σk ((b, (s_mb s + 6128, s_n s) :: skipn (S i) ents) :: rest)) by (rewrite <- Esk; exact HWP).
pose proof (rt_wfP_recs Σk b _ _ (skipn (S i) ents) rest k s HWPc Hk Hq eq_refl eq_refl) as HWP'.
eapply (cps_conseq asegs); [| intros cf Hcf; exact Hcf |].
2:{ intros cf Hcf. exists (recs Σk k). split; [exact Hcf|]. split; [exact HWP'|].
pose proof (recs_fields Σk k) as (X1 & X2 & _ & X4 & _ & _ & _ & X8 & _ & _ & X11 & X12 & X13).
split; [split; [rewrite X1; exact El|]; split; [rewrite X12; exact Elv|]; split; [rewrite X13; exact Efr|];
split; [rewrite X11; exact Ecr|]; split; [rewrite X8; exact Eql | split; [rewrite X4; exact Einit | exact Epo]]|].
rewrite X2. exact Hib. }
apply cps_pointwise. intros ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
rewrite Hent. cbn [fst].
change (MS (mkR (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (dl_usp p - 2288 - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (dl_usp p - 2288))
(Z_to_bv 64 INST) (Z_to_bv 64 (dl_usp p - 2288 - 104)) (Z_to_bv 64 (s_mb s + 6128)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
(dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom asegs))
with (ds_ms p b ents i s m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).

apply (cps_seq asegs _ (ASTA RTA Σk PMc (svc_mad p b ents i Σk k s m))).
{ apply (dl_evt Σk PMc _ _ MST). intros ms0 <-.
exact (ds_run1 p j b ib ents i rest Σk k s m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HOK HWP HS Hk Hq DM QB Hib Eb). }
apply (cps_seq asegs _ (ASTA RTA Σk PMc (fun ms => exists ms0, svc_mad p b ents i Σk k s m ms0 /\ ms = nretA ms0 (mad_eff s)))).
2:{ apply (cps_seq asegs _ (ASTA RTA Σk PMc (svc_mun p j b ents i rest Σk k s))).
- apply (dl_evt Σk PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
exact (ds_run2 p j b ib ents i rest Σk k s m HOK HWP HS Hk Hq DM QB Hib Eb ms0 Hms0).
- exact (ds_mun j Σk b ib ents i rest k s HWP HS Hib Eb Hk Hq). }

pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & _).
pose proof (ds_mad_geo Σk k s HG Hk) as (R1 & R2 & R3 & R5 & R6).
apply (AN Σk PMc (svc_mad p b ents i Σk k s m) (fun ms => exists ms0, svc_mad p b ents i Σk k s m ms0 /\ ms = nretA ms0 (mad_eff s))
(pbeg (shad (s_mb s))) (pend (shad (s_mb s + smsz (s_n s)))) FDO MST HL R1 R2 R3 R5 R6).
intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & mA & ws & lst & muw & mudw & -> & _).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
eexists. split; [exact Hms | reflexivity].
Qed.

End ISec.
End RL_dsec.
Export RL_dsec.

Module RL_drain_fin.
Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0i7 X0ib X0hx X0hv X0gj X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0df X0g3 X0ci X0cr X0cp X0cv X0cn X0ck X0cb X0e6.
Import RL_stmt RL_drain_ldefs RL_drain_istmt RL_drain_loop RL_drain_itemp RL_drain_batch RL_drain_rec RL_drain_xfer RL_drain_rhead RL_dsec_defs RL_dsec_runA RL_dsec_ret RL_dsec.

Definition dr_post (F : bvmap 5 word) (fc : bv 32) (Σ : rtsA) (PMc : Model -> Prop) (gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 : word) (lo usp : Z) (m : mem) :
config -> Prop :=
fun cf => exists Σ' : rtsA,
ASTA RTA Σ' PMc (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x46714) fc None m' (seg_rom asegs)
/\ ART_A Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2128)
/\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m') cf
/\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ rtA_pois Σ' = rtA_pois Σ.

Lemma rw_cells_agree_nw : forall (m m' : mem) A cs, rw_cells asegs m A cs ->
(forall a : word, A <= bv_unsigned a < A + Z.of_nat (cells_size cs) -> m' a = m a) -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs ((Hwf & (B0 & B1 & Hb)) & (W0 & W1 & Hw)) Hag.
pose proof (cells_bytes_length cs Hwf) as Hl.
split; [split; [exact Hwf|]|].
- split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite (Hag (wa (A + Z.of_nat i))); [exact (Hb i Hi)|].
rewrite wa_unsigned by lia. lia.
- split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hw i Hi) as X. unfold wview in X |- *.
rewrite (Hag (wa (A + i))); [exact X|]. rewrite wa_unsigned by lia. lia.
Qed.

Section DFin.
Variable p : dlp.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).

Theorem rec_from_R : forall (Σ' : rtsA) (m0 : mem) (s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 : word),
qrec_frame (dl_m0 p) C (Z_to_bv 64 0x4a080) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4 ->
qput_frame (dl_m0 p) (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6 ->
rt_pres (live Σ0) (frames Σ0) (usp + -2128) m0 (dl_m0 p) -> rt_wfP Σ' [] -> dl_sig p Σ' ->
cps asegs (ASTA RTA Σ' PMc (dl_R p Σ'))
(dr_post (dl_F p) (dl_fc p) Σ0 PMc (dl_gp p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) w0 w1 w2 w3 w4 w5 s6 lo usp m0).
Proof using HOK.
intros Σ' m0 s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 QF PF RP0 HWP HS.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
assert (HL : l_ACEIL (lay Σ') <= lo) by (rewrite El; exact N9).
assert (Esp1 : bv_unsigned (Z_to_bv 64 (usp + -2208)) = usp + -2208) by (apply unsigned_lit; lia).
assert (Esp2 : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
apply cps_pointwise.
intros ms (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & MI & ST & (G & WG & HGo) & RP & QR).

assert (QF1 : qrec_frame m (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80) (Z_to_bv 64 0x4a080) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4).
{ rewrite Esp1. replace (usp + -2208 + -80) with (usp - 2288) by lia. unfold qrec_frame in *.
apply (rw_cells_agree_nw (dl_m0 p) m _ _ QF). intros a Ha. apply RP. left. cbn [cells_size csize Nat.add Z.of_nat] in Ha. unfold USTACK_TOP. lia. }
assert (PF1 : qput_frame m (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6).
{ unfold qput_frame in *. apply (rw_cells_agree_nw (dl_m0 p) m _ _ PF). intros a Ha. apply RP. left.
cbn [cells_size csize Nat.add Z.of_nat] in Ha. unfold USTACK_TOP. lia. }
destruct QR as (QH & _).
replace (usp - 2288) with (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80) in QH, ST by (rewrite Esp1; lia).
eapply (cps_seq asegs).
{ eapply (dl_evt Σ' PMc _ _ MST). intros ms0 <-.
rewrite (ret_pc_even 0x47bc0); [|lia|reflexivity].
replace (Z_to_bv 64 (usp - 2288)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -80)) by (rewrite Esp1; f_equal; lia).
eapply evt_mono; [eapply (qrec_ret_spec (Z_to_bv 64 0x4a080) (Z_to_bv 64 (usp + -2208)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p)
a0 a1 a2 a3 a4 a5 a6 a7 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
(dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (Z_to_bv 64 0x47bc0) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) s2 s3 s4
_ _ _ _ (dl_F p) (dl_fc p) m lo)|].
1: exact QH. 1: exact QF1. 1: exact ST. 1: rewrite Esp1; lia. 1: exact N4. 1: exact MI.
intros ms' P. exact (conj P (conj A (conj MI (conj RP PF1)))). }
apply cps_pointwise.
intros ms ((t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1) & A0 & MI0 & RP0' & PF0).
rewrite Esp1 in MU1, ST1.
assert (HW1 : Forall (fun iv => lo <= fst iv /\ snd iv <= usp + -2128) [(usp + -2208 - 80, usp + -2208)]) by (repeat constructor; cbn [fst snd]; lia).
pose proof (artc_stk Σ' m m1 _ lo (usp + -2128) HG HL HW1 A Hdep HQB MU1 WM1) as A1.
pose proof (client_stk Σ' m m1 _ lo (usp + -2128) HG HL ltac:(lia) HW1 Hlive MU1) as RP1. rewrite Elv, Efr in RP1.
assert (PF2 : qput_frame m1 (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6).
{ rewrite Esp2. replace (usp + -2128 - 80) with (usp + -2208) by lia. unfold qput_frame in *.
apply (rw_cells_transport asegs _ m m1 _ _ PF0 MU1 WM1). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. lia. }
assert (ST1' : stk asegs m1 lo (bv_unsigned (Z_to_bv 64 (usp + -2128)) - 80)) by (rewrite Esp2; replace (usp + -2128 - 80) with (usp + -2208) by lia; exact ST1).
eapply (cps_seq asegs).
{ eapply (dl_evt Σ' PMc _ _ MST). intros ms0 <-.
rewrite (ret_pc_even 0x4a080); [|lia|reflexivity].
replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80)) by (rewrite Esp2; f_equal; lia).
eapply evt_mono; [apply (qput_C_spec (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 (dl_r5 p) (dl_r6 p)
(dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (Z_to_bv 64 0x4a080)
w0 w1 w2 w3 w4 w5 s6 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (dl_F p) (dl_fc p) m1 lo)|].
1: exact PF2. 1: exact ST1'. 1: rewrite Esp2; lia. 1: exact N4. 1: exact MI1.
intros ms' P. exact (conj P (conj A1 (conj RP0' RP1))). }
intros T0 cf Hcf Hk. apply Hk. exists Σ'.
split; [| split; [exact Elv | split; [exact Efr | split; [exact El | exact (conj Ecr (rtA_pois_eq _ _ Efr Epo))]]]].
unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms ((t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2)
& A1' & RP0'' & RP1').
rewrite Esp2 in MU2, ST2.
rewrite (ret_pc_even 0x46714); [|lia|reflexivity].
exists t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
assert (HW2 : Forall (fun iv => lo <= fst iv /\ snd iv <= usp + -2128) [(usp + -2128 - 80, usp + -2128)]) by (repeat constructor; cbn [fst snd]; lia).
pose proof (artc_stk Σ' m1 m2 _ lo (usp + -2128) HG HL HW2 A1' Hdep HQB MU2 WM2) as A2.
pose proof (client_stk Σ' m1 m2 _ lo (usp + -2128) HG HL ltac:(lia) HW2 Hlive MU2) as RP2. rewrite Elv, Efr in RP2.
split; [exact (c_ART Σ' m2 (rt_wfP_nil Σ' HWP) A2)|]. split; [exact MI2|]. split; [exact ST2|].
refine (rt_pres_trans _ _ _ _ m1 m2 _ RP2). refine (rt_pres_trans _ _ _ _ m m1 _ RP1').
refine (rt_pres_trans _ _ _ _ (dl_m0 p) m RP0 _). exact (rt_pres_mono _ _ (C + 32) (usp + -2128) _ _ RP ltac:(lia)).
Qed.

End DFin.

Theorem item_ok : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt p) -> forall p, dl_ok p -> item_stmt p.
Proof.
intros FC ISEC p HOK j Σk b ib ents i rest Hi HWP HS Hib Eb.
assert (Hq : qent_ok Σk (nth i ents (0, 0))).
{ pose proof HWP as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & Q7 & _) & _). unfold qentsP, qallP in Q7.
apply (proj1 (Forall_forall _ _) Q7). apply in_flat_map. exists (b, skipn i ents).
split; [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity|].
cbn [snd]. rewrite (skipn_nth_cons ents i (0, 0) Hi). left. reflexivity. }
destruct Hq as [(c & ic & Hc & Hic & Eh)|(s & Hs & Hsq & Hn & Eh)].
- apply (item_prim_ok p FC HOK j Σk b ib ents i rest c ic (snd (nth i ents (0, 0))) Hi HWP HS Hib Eb Hc Hic).
rewrite <- Eh. destruct (nth i ents (0, 0)); reflexivity.
- destruct (In_nth_error _ _ Hs) as (k & Hk).
apply (ISEC p HOK j Σk b ib ents i rest k s Hi HWP HS Hib Eb Hk Hsq). rewrite <- Eh, Hn. destruct (nth i ents (0, 0)); reflexivity.
Qed.

Lemma dd_switch : forall (Σ Σ' : rtsA) (PMc : Model -> Prop) (P : machine_state -> Prop), lay Σ' = lay Σ -> sec Σ' = sec Σ ->
rt_eager Σ' = rt_eager Σ -> aw Σ' = aw Σ -> cps asegs (ASTA RTA Σ PMc P) (ASTA RTA Σ' PMc P).
Proof.
intros Σ Σ' PMc P El Es Ee Ea T cf Hcf Hk. apply Hk. unfold ASTA in *. cbn [rt_allow ARTM RTA] in *.
replace (rtA_allow Σ') with (rtA_allow Σ) by (unfold rtA_allow; rewrite El, Ea; reflexivity).
eapply AST_conseq; [exact Hcf | intros ms X; exact X |]. intros mo (HM & HP). split; [|exact HP]. exact (artm_eq Σ Σ' mo El Es Ee HM).
Qed.

Theorem drain_rec : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt p) ->
forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
fdfs_only PMc -> mat_stable PMc ->
ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < X0fy.qbytes (ql Σ) ->
qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6 ->
stk asegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
mem_inv asegs m ->
0x10000000 < X0id.qbytes (qg Σ ++ ql Σ) ->
cps asegs (ASTA RTA Σ PMc (eq (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
(dr_post F fc Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
intros FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr.
pose proof (xr_geo Σ HW) as (HG & _).
pose proof (rt_wfP_start Σ HW HC) as HWP1.
eapply (cps_seq asegs).
{ eapply (dl_evt Σ PMc _ _ MST). intros ms <-.
exact (rr_evt Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
HA HW HC HBY FR ST HLO HLO2 HSP MI HBYr). }
eapply (cps_seq asegs); [exact (dd_switch Σ (set_q Σ [] (rec_r (qg Σ ++ ql Σ) QMIN)) PMc _ eq_refl eq_refl eq_refl eq_refl)|].
apply cps_pointwise.
intros ms (t0' & t1' & t2' & s0' & s1' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & t3' & t4' & t5' & t6' & m3 & -> & A3 & QR3 & QF3 & PF3
& ST3 & MI3 & WM3 & RP3).
pose (p := mkDLP Σ m3 usp lo PMc gp s10 s11 F fc s0' s1' s2' s3' s4' s5 (Z_to_bv 64 0x100000) s7 s8 s9).
assert (HOK : dl_ok p) by (split; [exact FDO|]; split; [exact MST|]; split; [exact HLO|]; split; [exact HLO2|]; split; [exact HSP | exact HG]).
assert (Einit : ca_init Σ = true).
{ destruct (ca_init Σ) eqn:E; [reflexivity|]. exfalso.
pose proof HW as (_ & HR & _ & _ & (_ & _ & Q4 & _) & _). pose proof (proj2 (proj2 (proj2 (proj2 (proj2 HR)))) E 24) as E24.
destruct (qg Σ ++ ql Σ) as [|b0 bs] eqn:EG.
- cbn in HBYr. lia.
- assert (Hb0 : In b0 (ql Σ ++ qg Σ)) by (apply (Permutation_in _ (Permutation_app_comm (qg Σ) (ql Σ))); rewrite EG; left; reflexivity).
destruct (proj1 (Forall_forall _ _) Q4 b0 Hb0) as (ib & Hib & _). rewrite E24 in Hib. destruct ib; discriminate. }
assert (HS1 : dl_sig p (set_q Σ [] (rec_r (qg Σ ++ ql Σ) QMIN))) by (repeat split; [exact Einit]).
pose proof (item_ok FC ISEC p HOK) as ITEM. pose proof (batch_ok p FC HOK) as BATCH.
eapply (cps_seq asegs).
{ eapply (cps_conseq asegs); [exact (dl_from_E p HOK ITEM BATCH _ (rec_x (qg Σ ++ ql Σ) QMIN) HWP1 HS1) | | intros cf Hcf; exact Hcf].
intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms E. rewrite <- E. exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6', m3. split; [reflexivity|].
split; [exact A3|]. split; [exact QR3|]. split; [exact ST3|]. split; [exact MI3|].
split; [exists []; split; [exact (wmono_out_nil m3 m3 (wmono_refl asegs m3)) | constructor]|].
intros a _. reflexivity. }
apply dl_cps_ex. intros Σ' (HWP' & HS').
exact (rec_from_R p HOK Σ' m s2 s3 s4 w0 w1 w2 w3 w4 w5 s6 QF3 PF3 RP3 HWP' HS').
Qed.

Theorem drain_ok : fixed_commit_node -> (forall p, dl_ok p -> item_sec_stmt p) ->
forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
fdfs_only PMc -> mat_stable PMc ->
ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < X0fy.qbytes (ql Σ) ->
qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) w0 w1 w2 w3 w4 w5 s6 ->
stk asegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
mem_inv asegs m ->
cps asegs (ASTA RTA Σ PMc (eq (xms0 Σ ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp)))
(dr_post F fc Σ PMc gp s7 s8 s9 s10 s11 w0 w1 w2 w3 w4 w5 s6 lo usp m).
Proof.
intros FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp w0 w1 w2 w3 w4 w5 s6
FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI.
destruct (Z_le_gt_dec (X0id.qbytes (qg Σ ++ ql Σ)) 0x10000000) as [Hx|Hr].
- eapply (cps_conseq asegs);
[exact (drain_xfer Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
w0 w1 w2 w3 w4 w5 s6 FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI Hx) | intros cf X; exact X |].
intros cf (Σ' & Hcf & E1 & E2 & E3 & E4). exists Σ'. split; [|exact (conj E1 (conj E2 (conj E3 E4)))].
unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & X1 & X2 & _ & X4 & X5).
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [reflexivity | exact (conj X1 (conj X2 (conj X4 X5)))].
- exact (drain_rec FC ISEC Σ PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
w0 w1 w2 w3 w4 w5 s6 FDO MST HA HW HC HBY FR ST HLO HLO2 HSP MI ltac:(lia)).
Qed.
End RL_drain_fin.
Export RL_drain_fin.
