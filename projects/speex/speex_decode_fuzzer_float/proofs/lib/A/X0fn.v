(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2 X0mx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1sa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X0j1 X0gi X0hr X0j3 X0hi
X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0j6 X0gd X0go X0i7
X0ge X0hs X0gu X0fy X0fg X0da X0g4 X0d8 X0fq X0d7 X0eo X0f0 X0e4 X0d9
X0e5 X0db X0j5 X0ft X0id X0hz X0e8 X0dc X0e6 X0dd X0de X0dg X0di X0df
X0dk X0dq X0dx X0dy X0i3 X0i0 X0dl X0dn X0i1 X0i2 X0ie X0dj X0dm X0do
X0e0 X0fd X0fc X0fe X0fi X0c7 X0dp X0dz X0e1 X0f7 X0f4 X0g3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0fm.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X19p X16y X179 X18s X16z X18d X17f X16j X161 X13v X16p X13t X16b X13s X159 X15l X14p X13u X14q X13w X19o X16e X18y X18k X14t X13x X14r X13y X13z X141 X143 X140 X145 X14b X14i X14j X18o X18l X146 X148 X18m X18n X18z X144 X147 X149 X14l X15y X15x X15z X163 X12s X14a X14k X14m X15s X15p X16o.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X167.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X179 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X159 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X141 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X143 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X140 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X145 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X146 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X148 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X144 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X147 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X149 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X163 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16o.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X167.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Module RL_A2.
Import X12c X0j9 X14x X0r0 X0ra X0v9 X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X19p X16y X179 X18s X16z X18d X17f X16j X161 X13v X16p X13t X16b X13s X159 X15l X14p X13u X14q X13w X19o X16e.
Import RL_stmt .

Definition icpt_frame (m : mem) (usp : Z) (ra s0 s1 s2 s3 s4 s5 : word) : Prop :=
(exists s4r s3r s2r s1r s0r, rw_cells bsegs m (usp + -2128) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x466f0)])
/\ (exists jr, rw_cells bsegs m (usp + -2080) [CB 8 jr; C8 (Z_to_bv 64 0x68770)])
/\ (exists jq, rw_cells bsegs m (usp + -2064) [CB 8 jq])
/\ (exists w, rw_cells bsegs m (usp + -2056) [C8 (Z_to_bv 64 (usp + -2040)); C8 w])
/\ (exists ws, u64arr bsegs m (usp + -2040) ws /\ length ws = 255%nat).

Lemma icpt_frame_transport : forall W (m m' : mem) usp ra s0 s1 s2 s3 s4 s5, icpt_frame m usp ra s0 s1 s2 s3 s4 s5 ->
munch W m m' -> wmono bsegs m m' -> disjoint_from W (usp - 2128) 2128 -> icpt_frame m' usp ra s0 s1 s2 s3 s4 s5.
Proof.
intros W m m' usp ra s0 s1 s2 s3 s4 s5 ((s4r & s3r & s2r & s1r & s0r & F1) & (jr & F2) & (jq & F3) & (w & F4) & (ws & F5 & F5l)) MU WM HD.
split; [|split; [|split; [|split]]].
- exists s4r, s3r, s2r, s1r, s0r. apply (rw_cells_transport bsegs W m m' _ _ F1 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
- exists jr. apply (rw_cells_transport bsegs W m m' _ _ F2 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
- exists jq. apply (rw_cells_transport bsegs W m m' _ _ F3 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
- exists w. apply (rw_cells_transport bsegs W m m' _ _ F4 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
- exists ws. split; [|exact F5l]. apply (u64arr_transport bsegs W m m' _ _ F5 MU WM). rewrite F5l.
apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | cbn; lia].
Qed.

Lemma icpt_frame_agree : forall (m m' : mem) usp ra s0 s1 s2 s3 s4 s5, icpt_frame m usp ra s0 s1 s2 s3 s4 s5 ->
(forall a : word, usp - 2128 <= bv_unsigned a < usp -> m' a = m a) -> icpt_frame m' usp ra s0 s1 s2 s3 s4 s5.
Proof.
intros m m' usp ra s0 s1 s2 s3 s4 s5 ((s4r & s3r & s2r & s1r & s0r & F1) & (jr & F2) & (jq & F3) & (w & F4) & (ws & F5 & F5l)) AG.
split; [|split; [|split; [|split]]].
- exists s4r, s3r, s2r, s1r, s0r. apply (X0ra.rw_cells_agree_nw bsegs m m' _ _ F1). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
- exists jr. apply (X0ra.rw_cells_agree_nw bsegs m m' _ _ F2). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
- exists jq. apply (X0ra.rw_cells_agree_nw bsegs m m' _ _ F3). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
- exists w. apply (X0ra.rw_cells_agree_nw bsegs m m' _ _ F4). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
- exists ws. split; [|exact F5l]. apply (X0ra.u64arr_agree_nw bsegs m m' _ _ F5). intros a Ha. apply AG. rewrite F5l in Ha. cbn in Ha. lia.
Qed.

Definition sA_run_post (Σ : rtsA) (c : Z) (i : nat) (n usp lo : Z) (tr : list Z) (gp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (l_T (lay Σ) + 208))
(Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 n) a5' a6' a7'
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (l_T (lay Σ) + 208))
(Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m' (seg_rom bsegs)
/\ ARTc (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) m'
/\ mem_inv bsegs m' /\ wmono bsegs m m'
/\ munch (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp) m m'
/\ stk bsegs m' lo (usp + -2208)
/\ qput_frame m' (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) s0
(Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16)) s2 s3 s4
s5 s6.

Lemma dp_hash1 : forall D tr, dep_inv D -> hash_of (d_hs (fst (depot_put D tr))) 1 = hash_of (d_hs D) 1.
Proof.
intros D tr (_ & _ & H1 & _). destruct (Z.eqb_spec (find_of (d_hs D) (depot_hash tr)) 0) as [E|E].
- rewrite (depot_put_miss D tr E). cbn [fst d_hs]. apply hash_of_snoc_old. unfold d_n in H1. lia.
- rewrite (depot_put_hit D tr E). reflexivity.
Qed.

Section SegRun.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n usp lo : Z) (tr : list Z) (tb : list word) (s0 s2 s3 s4 s5 : word).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis Hn1 : 1 <= n.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Husp : usp + 16 <= USTACK_TOP.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x10000 <= usp.
Hypothesis ST : stk bsegs m lo (usp + -2128).
Hypothesis MI : mem_inv bsegs m.
Hypothesis BC : rw_cells bsegs m (usp + -2056) [C8 (Z_to_bv 64 (usp + -2040)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))].
Hypothesis TB : u64arr bsegs m (usp + -2040) (wr_trace tr tb).
Hypothesis HTB : length tb = 255%nat.
Hypothesis Htr : In tr T_MAIN /\ (1 <= length tr <= 5)%nat.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation S := (ClassSize c).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation W := (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp).

Lemma sr_tcx : 0 < TCX /\ TCX + 0x10000 <= l_ACEIL L /\ (TCX + 0x10000 <= PRB \/ PRB + 0x2000011000 <= TCX)
/\ (TCX + 0x10000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= TCX) /\ (TCX + 0x10000 <= 0x10000 \/ SEGTOP_A <= TCX)
/\ (TCX + 0x10000 <= T \/ T + 4096 <= TCX).
Proof using HA.
clear - HA. pose proof (geo_grant Σ m HA TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & _ & X3 & X4 & X5).
pose proof (geo_apart Σ m HA 0 3 _ _ ltac:(lia) eq_refl eq_refl) as A03. pose proof (geo_apart Σ m HA 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23.
cbn [fst snd] in *. unfold apart in *. split; [exact X1|]. split; [exact X3|]. split; [lia|]. split; [exact X4|]. split; [exact X5|]. lia.
Qed.

Lemma sr_tr : In tr T_MAIN /\ (1 <= length tr <= 5)%nat /\ Forall rng64 tr.
Proof using Htr.
clear - Htr. destruct Htr as (H1 & H2). split; [exact H1|]. split; [exact H2|]. exact (T_MAIN_rng64 tr H1).
Qed.

Lemma fl_c8_of_stk : forall (m0 : mem) a, stk bsegs m0 a (a + 8) -> exists w, rw_cells bsegs m0 a [C8 w].
Proof.
clear. intros m0 a St. destruct (stk_bytes bsegs m0 a (a + 8) St ltac:(lia)) as (bs & Hl & Hb). replace (a + 8 - a) with 8 in Hl by lia.
exists (le_bytes_to_word bs). split; [split|].
- cbn. tauto.
- cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite fl_le8_of_bytes by lia. exact Hb.
- cbn [cells_size csize Nat.add]. destruct St as (S0 & S1 & Sw). split; [lia|]. split; [lia|]. intros j Hj. exact (proj1 (Sw (a + j) ltac:(lia))).
Qed.

Lemma fl_two_c8 : forall (m0 : mem) a, stk bsegs m0 a (a + 16) -> exists w1 w2, rw_cells bsegs m0 a [C8 w1; C8 w2].
Proof.
clear. intros m0 a St. destruct (stk_split bsegs m0 a (a + 8) (a + 16) St ltac:(lia)) as [S1 S2].
destruct (fl_c8_of_stk m0 a S1) as (w1 & H1). destruct (fl_c8_of_stk m0 (a + 8) ltac:(replace (a + 8 + 8) with (a + 16) by lia; exact S2)) as (w2 & H2).
exists w1, w2. change [C8 w1; C8 w2] with ([C8 w1] ++ [C8 w2]). apply rwc_app. split; [exact H1|]. exact H2.
Qed.

Lemma sr_geo2 : shad (M + 16) + ru8 n / 8 <= shad (AB + S) /\ SHB <= shad (M + 16) /\ 0 <= ru8 n / 8
/\ shad (rb SB c) <= shad (M + 16) /\ shad (M + 16) + ru8 n / 8 <= shad (rb SB c + 2 ^ 32).
Proof using HA Hc Hn Hn1.
clear - HA Hc Hn Hn1.
pose proof (sa_geo Σ m c i n HA Hc Hn Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
& K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
pose proof (fk_shad_mono (rb SB c) AB K7) as E1. pose proof (fk_shad_mono (AB + S) (rb SB c + 2 ^ 32)) as E2.
assert (AB + S <= rb SB c + 2 ^ 32) by (clear - K8 K10; unfold kUserCap in *; lia). specialize (E2 H).
split; [exact K16|]. split; [exact K30|]. split; [exact K40|]. split; [lia|]. lia.
Qed.

Lemma sr_M16 : M mod 16 = 0.
Proof using HA Hc.
clear - HA Hc. pose proof (geo_prb Σ m HA) as (_ & _ & P3). pose proof (ClassSize_range c Hc) as (_ & Hm). pose proof (rz_facts n) as (R1 & _).
unfold p_abeg. apply Z.mod_divide in P3, Hm, R1; try (clear; lia). destruct P3 as [q1 E1]. destruct Hm as [q2 E2]. destruct R1 as [q3 E3].
rewrite E1, E2, E3. replace (q1 * 2 ^ 16 + c * 2 ^ 32 + Z.of_nat i * (q2 * 32) + q3 * 16 - 16) with ((q1 * 4096 + c * 2 ^ 28 + Z.of_nat i * q2 * 2 + q3 - 1) * 16) by ring.
apply Z.mod_mul. lia.
Qed.

Lemma segA_run : forall gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32),
evt bsegs (sA_run_post Σ c i n usp lo tr gp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
(MS (mkR (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0 (Z_to_bv 64 (M + 16))
(Z_to_bv 64 INST) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 1) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom bsegs)).
Proof.
intros gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc.
pose proof (sa_geo Σ m c i n HA Hc Hn Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
& K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
pose proof (sa_disj Σ m HA) as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
pose proof sr_tcx as (X1 & X3 & XP & X4 & X5 & XT).
pose proof sr_tr as (TRM & TRL & TRR).
pose proof sr_geo2 as (G1 & G2 & G3 & G4 & G5).
pose proof sr_M16 as HM16.

destruct (ART_chunk Σ m HA) as [CP _]. destruct (CP c i (CkAlloc n) Hc Hn) as (WrA & (b1 & ctx & Hb1 & HD) & LCH & SHA1 & SHA2).
clear CP.

pose proof (ART_consts Σ m HA) as (IC & MMG & TC & M2S & PS & SC & CC & ICR).
destruct ICR as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18 & I19 & I20
& I21 & I22 & I23 & I24 & I25 & I26 & I27 & I28 & I29 & I30 & I31 & I32 & I33 & I34 & I35 & I36 & I37 & I38).
clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22 I24 I25 I26 I27 I28 I29 I30 I37 I38.

pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
pose proof (ART_dep Σ m HA) as DREP. unfold dep_rep in DREP.

destruct (fl_CB_of_wr m AB S (M + 16) 8 WrA ltac:(lia) ltac:(cbn; lia)) as (uw & UW).
destruct (fl_two_c8 m (T + 2824) ltac:(destruct (stk_split bsegs m (T + 2768) (T + 2824) (T + 3168) I32 ltac:(lia)) as [_ X];
destruct (stk_split bsegs m (T + 2824) (T + 2840) (T + 3168) X ltac:(lia)) as [X' _];
replace (T + 2824 + 16) with (T + 2840) by lia; exact X')) as (fr & fd & STS).
pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1.
assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; exact Rb1).
rewrite <- Eb in HD. clear Eb.
assert (RSP : 0 <= usp + -2128 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).

eapply evt_cut.
{ apply (dealloc_p1_spec (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp t0 t1 t2 s0 (Z_to_bv 64 (M + 16)) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
M n (bv_unsigned b1) (usp + -2056) TCX T lo ctx fr fd uw); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
all: try exact ST.
all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
all: try (clear - K33 K4 HLO; lia).
all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
all: try (clear - X3 HLO; lia). all: try (clear - K20 HLO; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - ATP K32 K33; lia). all: try (clear - XP K32 K33; lia).
all: try (clear - HLO2; lia). all: try (clear - Husp; unfold USTACK_TOP in *; lia). }
intros ms2 P2.
destruct P2 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & fr' & fd' & m2 & -> & MU2 & WM2 & MI2 & HD2 & UW2 & STS2 & ST2).
rewrite (unsigned_lit (usp + -2128)) in MU2, ST2 by exact RSP.
assert (MW2 : munch W m m2).
{ lazymatch type of MU2 with munch ?W2 _ _ => apply (munch_weaken W2 _ m m2); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU2] end. }
pose proof (sa_consts Σ m c i n usp HA Hc Hn Hn1 Hsp m2 MW2 WM2) as CR2.
destruct CR2 as (_ & _ & TC2 & _ & _ & _ & _ & ICR2).
destruct ICR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J31 & _ & J33 & _ & _ & _ & _ & _).
lazymatch type of MU2 with munch ?W2 _ _ =>
apply (rw_cells_transport bsegs W2 m m2 _ _) in BC; [| exact MU2 | exact WM2 |];
[| cbn [disjoint_from cells_size csize Nat.add]; clear - K33 K4 K20 Hsp; repeat split; try exact I; lia];
apply (u64arr_transport bsegs W2 m m2 _ _) in TB; [| exact MU2 | exact WM2 |];
[| rewrite wr_trace_length by (rewrite HTB; clear - TRL; lia); rewrite HTB; cbn [disjoint_from]; clear - K33 K4 K20 Hsp;
repeat split; try exact I; lia] end.
lazymatch type of MU2 with munch ?W2 _ _ => apply (dep_rep_transport W2 L (dep Σ) m m2) in DREP; [| exact DOK | exact MU2 | exact WM2 |] end.
2:{ split; [|split].
- unfold dsjl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd disjoint_from]; repeat split; try exact I;
first [ (left; clear - K2 K32; unfold SEGTOP_A in *; lia) | (clear - T5 K19; unfold SEGTOP_A in *; lia)
| (left; clear - Hsp K4 K2; unfold SEGTOP_A in *; lia) ].
- cbn [disjoint_from]. repeat split; try exact I; [clear - APD K32 K33; lia | clear - ATD; lia | clear - K23 Hsp; lia].
- cbn [disjoint_from]. repeat split; try exact I; [clear - APS K32 K33; lia | clear - ATS; lia | clear - K26 Hsp; lia]. }
rewrite wr_trace_split in TB. replace (usp + -2040) with (usp + -2056 + 16) in BC, TB by lia.
rewrite <- (length_map (Z_to_bv 64) tr) in BC.

eapply evt_cut.
{ apply (qchunk_spec (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp u0 u1 u2 s0 (Z_to_bv 64 (M + 16)) u3 u4 u5 u6
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u7 u8 u9 u10 F fc m2
M n (bv_unsigned b1) (usp + -2056) TCX T lo ctx (Z_to_bv 64 18446744069414584320) (dep Σ)
(DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB (map (Z_to_bv 64) tr) (skipn (length tr) tb));
try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
all: try exact ST2.
all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
all: try (clear - K33 K4 HLO; lia).
all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
all: try (clear - X3 HLO; lia). all: try (clear - K20 HLO; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - APD K32 K33; lia). all: try (clear - APS K32 K33; lia).
all: try (clear - HLO2; lia). all: try (clear - Husp; unfold USTACK_TOP in *; lia).
all: try (rewrite length_map; clear - TRL; lia).
all: try (rewrite <- wr_trace_split, wr_trace_length by (rewrite HTB; clear - TRL; lia); exact HTB).
all: try (exact (depot_ok_mono _ _ _ _ _ DOK HLO)).
all: try (rewrite length_map; clear - DT TRL; lia).
all: try (rewrite map_unsigned_lits by exact TRR; unfold DEP_BK; right; apply in_map_iff; exists tr; split; [reflexivity | exact TRM]). }
intros ms3 P3.
destruct P3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & m3 & -> & MU3 & WM3 & MI3 & W16 & REP3 & TB3 & ST3).
rewrite (unsigned_lit (usp + -2128)) in MU3, ST3 by exact RSP.
assert (MW3 : munch W m m3).
{ apply (munch_trans _ m m2 m3 MW2).
lazymatch type of MU3 with munch ?W3 _ _ => apply (munch_weaken W3 _ m2 m3); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU3] end. }
pose proof (wmono_trans bsegs _ _ _ WM2 WM3) as WM23.
pose proof (sa_consts Σ m c i n usp HA Hc Hn Hn1 Hsp m3 MW3 WM23) as CR3.
destruct CR3 as (_ & _ & _ & _ & PS3 & _ & _ & ICR3).
destruct ICR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& _ & _ & K23' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K35' & K36' & _ & _).
apply (rwc_app bsegs _ _ [C8 (Z_to_bv 64 268435456)]) in K35'. destruct K35' as [QM K35']. cbn [cells_size csize Nat.add] in K35'.
apply (rwc_app bsegs _ _ [C8 (Z_to_bv 64 241591905)]) in K35'. destruct K35' as [_ QC]. cbn [cells_size csize Nat.add] in QC.
change (i_q_max + Z.of_nat 8 + Z.of_nat 8) with 1058688 in QC. change i_q_max with 1058672 in QM.

lazymatch type of MU3 with munch ?W3 _ _ =>
apply (rw_cells_transport bsegs W3 m2 m3 _ _) in HD2; [| exact MU3 | exact WM3 |];
[| cbn [disjoint_from cells_size csize Nat.add];
repeat split; try exact I;
first [ (left; clear; lia) | (right; clear - K2 K32; unfold SEGTOP_A in *; lia) | (clear - APD K32 K33; lia) | (clear - APS K32 K33; lia)
| (left; clear - K33 K4 Hsp; lia) ] ] end.

apply bytes_at_app in SHA1. destruct SHA1 as [_ SHU]. rewrite farun_lenZ in SHU by lia. rewrite <- K15 in SHU.
assert (SHC : rw_cells bsegs m (shad (M + 16)) [CB (length (ushadow n)) (ushadow n)]).
{ destruct (ART_prim Σ m HA c Hc) as (_ & _ & _ & _ & _ & _ & SST).
apply (fl_CB_of_bytes m _ _ _ _ SHU SST G4). rewrite fl_ushadow_len by lia. exact G5. }
replace (length (ushadow n)) with (Z.to_nat (ru8' n / 8)) in SHC by (unfold ru8'; pose proof (fl_ushadow_len n ltac:(lia)) as U; unfold ru8 in U; lia).
lazymatch type of MU2 with munch ?W2 _ _ =>
apply (rw_cells_transport bsegs W2 m m2 _ _) in SHC; [| exact MU2 | exact WM2 |];
[| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (unfold ru8'; apply Z.div_pos; lia);
change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (left; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (clear - T4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (left; clear - K27 K31 Hsp; lia) ] ] end.
lazymatch type of MU3 with munch ?W3 _ _ =>
apply (rw_cells_transport bsegs W3 m2 m3 _ _) in SHC; [| exact MU3 | exact WM3 |];
[| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (unfold ru8'; apply Z.div_pos; lia);
change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (left; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (right; clear - K30; unfold SHB in *; lia)
| (clear - D4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (clear - S4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (left; clear - K27 K31 Hsp; lia) ] ] end.

eapply evt_mono.
{ apply (qput_A_spec (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) v0 v1 v2 s0 (Z_to_bv 64 (M + 16)) v3 v4
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v5 v6 v7 v8 F fc m3
(T + 80) (T + 208) (usp + -2056) M n (bv_unsigned b1) lo ctx (ushadow n)); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
all: try exact ST3.
all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
all: try (change (ru8' n) with (ru8 n); clear - K12 K39 K4 K28; unfold kHighMemEnd; lia).
all: try (change (ru8' n) with (ru8 n); clear - K12 K39 K4 HLO; lia).
all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
all: try (clear - HLO2; lia).
all: try (clear - HA HLO; pose proof (rta_sp0_win Σ m HA); unfold l_ACEIL, rtA_sp0, STACK_WIN, kHighShadowEnd in *; lia). }
intros ms4 P4.
destruct P4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & m4 & -> & MU4 & WM4 & MI4 & SH4 & FR4 & ST4).
rewrite (unsigned_lit (usp + -2128)) in MU4, ST4, FR4 by exact RSP.
assert (MW4 : munch W m m4).
{ apply (munch_trans _ m m3 m4 MW3).
lazymatch type of MU4 with munch ?W4 _ _ => apply (munch_weaken W4 _ m3 m4); [unfold W_A1; clear - Hsp; change (ru8' n) with (ru8 n); solve_sub_fp | exact MU4] end. }
pose proof (wmono_trans bsegs _ _ _ WM23 WM4) as WM24.

assert (HQ : qhdr3 m4 M n).
{ lazymatch type of MU4 with munch ?W4 _ _ =>
apply (rw_cells_transport bsegs W4 m3 m4 _ _) in HD2; [| exact MU4 | exact WM4 |];
[| cbn [disjoint_from cells_size csize Nat.add]; change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (right; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (left; clear - K33 K4 Hsp; lia) ] ];
apply (rw_cells_transport bsegs W4 m3 m4 _ _) in W16; [| exact MU4 | exact WM4 |];
[| cbn [disjoint_from cells_size csize Nat.add]; change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (right; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (left; clear - K33 K4 Hsp; lia) ] ] end.
exists (Z_to_bv 8 (bv_unsigned b1)), ctx, (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr))))).
split; [rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite (Z.mod_small (bv_unsigned b1) 256) by exact Rb1; exact Hb1|].
change [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx;
C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]
with ([C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ++
[C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]).
apply rwc_app. split; [exact HD2|]. cbn [cells_size csize Nat.add]. exact W16. }

rewrite map_unsigned_lits in REP3 by exact TRR.
lazymatch type of MU4 with munch ?W4 _ _ =>
apply (depot_rep_frame _ _ _ _ lo W4 m3 m4) in REP3; [| | exact MU4 | exact WM4 | | | | | |] end.
2:{ apply (qc_depot_ok_put_ok _ _ _ _ _ (depot_ok_mono _ _ _ _ _ DOK HLO) DN). clear - DT TRL; lia. }
all: try (cbn [disjoint_from]; change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (right; clear - K30; unfold SHB in *; lia) | (left; clear - K2 Hsp K4; unfold SEGTOP_A in *; lia)
| (clear - D4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (clear - S4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (left; clear - K23 Hsp; lia) | (left; clear - K26 Hsp; lia) ]).
pose proof (segA_ART Σ m c i n usp HA Hc Hn Hn1 Hsp m4 (fst (depot_put (dep Σ) tr)) MW4 WM24 HQ SH4 REP3
(qc_depot_ok_put_ok (dep Σ) tr DNB SSB (l_ACEIL L) DOK DN ltac:(clear - DT TRL; lia)) (dep_inv_put (dep Σ) tr DINV TRM ltac:(clear - TRL; lia))
(dp_hash1 _ _ DINV)) as ART4.
unfold sA_run_post. do 10 eexists. exists m4. split.
{ rewrite (unsigned_lit (usp + -2128)) by exact RSP. replace (usp + -2128 + -80) with (usp + -2208) by lia. reflexivity. }
split; [exact ART4|]. split; [exact MI4|]. split; [exact WM24|]. split; [exact MW4|].
split; [replace (usp + -2208) with (usp + -2128 - 80) by lia; exact ST4|].
replace (usp + -2208) with (usp + -2128 - 80) by lia. exact FR4.
Qed.

End SegRun.
End RL_A2.
Export RL_A2.

Module RL_G.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X18s X18k X16z X18d X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141.
Import RL_stmt RL_A2.

Definition enq_post (Σ2 : rtsA) (live0 : list (Z * Z)) (frames0 : list (Z * nat)) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w1 : word) (m' : mem),
ms = enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m'
/\ ARTc Σ2 m' /\ rt_wfx Σ2 /\ rt_count Σ2 /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo (bv_unsigned sp + -2208)
/\ rt_pres live0 frames0 (bv_unsigned sp) m m'
/\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
/\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ2) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46800)
s0 w1 s2 s3 s4 s5 s6.
End RL_G.
Export RL_G.

Module RL_FH.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X18s X18k X16z X18d X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141 X143 X140.
Import RL_stmt RL_A2 RL_G.
Import X0ra.

Definition rl_ret_st (usp : Z) (gp s0 w1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) y0 y1 y2 s0 w1 y3 y4 y5 y6 y7 y8 y9 y10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y11 y12 y13 y14) F (Z_to_bv 64 0x46800) fc None m (seg_rom bsegs).

Definition fin_post (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m5 : mem) : machine_state -> Prop :=
fun ms => exists (w1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m' : mem),
ms = rl_ret_st (bv_unsigned sp) gp s0 w1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F fc m'
/\ ART_A Σ2 m' /\ mem_inv bsegs m' /\ wmono bsegs m5 m' /\ stk bsegs m' lo (bv_unsigned sp + -2128)
/\ munch [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)] m5 m'.

Lemma ret_tail : forall (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
t3 t4 t5 t6 w1 wc ws : word) (F : bvmap 5 word) (fc : bv 32) (m5 : mem) (lo : Z),
geo_ok Σ2 -> ARTc Σ2 m5 -> rt_wfx Σ2 -> rt_count Σ2 -> X16j.qbytes (ql Σ2) <= 0x100000 ->
mem_inv bsegs m5 -> stk bsegs m5 lo (bv_unsigned sp + -2208) -> l_ACEIL (lay Σ2) <= lo -> lo + 0x10000 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP ->
qput_frame m5 (bv_unsigned sp + -2208) wc ws (Z_to_bv 64 0x46800) s0 w1 s2 s3 s4 s5 s6 ->
evt bsegs (fin_post Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m5)
(enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5).
Proof.
intros Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w1 wc ws F fc m5 lo
HG ART5 HWX HC HBY MI5 ST5 HLO HLO2 Husp FR5.
set (usp := bv_unsigned sp) in *.
pose proof (fk_aceil Σ2 HG) as (X1 & X2).
assert (RSP2 : 0 <= usp + -2128 < 2 ^ 64) by (clear - HLO HLO2 Husp X1; unfold USTACK_TOP, SHB in *; lia).
pose proof ART5 as (_ & _ & _ & _ & _ & QR & _). destruct QR as (QT & _).
pose proof QT as QT'. apply (proj1 (qcache_rep_iff _ _ _)) in QT'. destruct QT' as (QH & _).
unfold enq_ret_st.
replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80))
by (rewrite (unsigned_lit (usp + -2128)) by exact RSP2; f_equal; lia).
replace (usp + -2208) with (usp + -2128 - 80) in ST5, FR5 by lia.
pose proof (qbytes_nonneg _ _ (qwf_ql_x Σ2 HWX)) as QB0.
eapply evt_mono.
{ apply (qput_B_ret_spec (Z_to_bv 64 0x46800) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11
t3 t4 t5 t6 ra0 s0 w1 s2 s3 s4 s5 s6 wc ws F fc m5 (l_T (lay Σ2) + 80) (X18y.qbytes (ql Σ2)) lo
(Z_to_bv 64 (Z.of_nat (length (ql Σ2)))) (Z_to_bv 64 (qfirst (ql Σ2))) (Z_to_bv 64 (qlast (ql Σ2))));
try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP2.
all: try exact ST5. all: try exact FR5. all: try (clear - HLO2; lia). all: try (clear - X1 HLO; unfold SHB in *; lia).
rewrite qbytes_eq. clear - QB0 HBY. rewrite qbytes_eq in QB0. lia. }
intros ms6 P6. destruct P6 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6).
rewrite (unsigned_lit (usp + -2128)) in MU6, ST6 by exact RSP2. rewrite (ret_pc_even 0x46800) by (first [reflexivity | lia]).
assert (MU6' : munch [(usp - 2208, usp - 2128)] m5 m6).
{ lazymatch type of MU6 with munch ?W6 _ _ => apply (munch_weaken W6 _ m5 m6); [clear - HLO2; solve_sub_fp | exact MU6] end. }
unfold fin_post, rl_ret_st. exists w1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m6. split; [reflexivity|].
split; [|split; [exact MI6 | split; [exact WM6 | split; [exact ST6 | exact MU6']]]].
apply c_ART; [exact (rt_wf_of_x Σ2 HWX HC ltac:(clear - HBY; unfold QMAX_L; lia))|].
apply (ARTc_stack Σ2 (usp - 2208) (usp - 2128) HG ltac:(clear - HLO HLO2; lia) m5 m6 ART5 MU6' WM6).
- destruct HWX as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
- destruct HWX as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK.
Qed.

Definition rl_postF (Σ : rtsA) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(p lo : Z) (m : mem) : config -> Prop :=
fun c' => exists (Σ' : rtsA),
ASTA RTA Σ' PMc (fun ms => exists (w1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m' : mem),
ms = rl_ret_st (bv_unsigned sp) gp s0 w1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F fc m'
/\ ART_A Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -2128)
/\ rt_pres (live_remove p (live Σ)) (frames Σ) (bv_unsigned sp) m m'
/\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5) c'
/\ live Σ' = live_remove p (live Σ) /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ rtA_pois Σ' = rtA_pois Σ.

Section Fin.
Hypothesis DRAIN : drain_stmt.

Theorem fin_from_enq : forall (Σ Σ2 : rtsA) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (lo p : Z) T cf,
fdfs_only PMc -> mat_stable PMc ->
live Σ2 = live_remove p (live Σ) -> frames Σ2 = frames Σ -> lay Σ2 = lay Σ -> credit Σ2 = credit Σ -> rtA_pois Σ2 = rtA_pois Σ ->
l_ACEIL (lay Σ) <= lo -> lo + 0x10000 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
AST SEGTOP_A (rtA_allow Σ2) (enq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(fun mo => ARTM_A Σ2 mo /\ PMc mo) cf ->
(forall c', rl_postF Σ PMc F fc ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m c' -> realizes bsegs c' T) ->
realizes bsegs cf T.
Proof.
intros Σ Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p T cf FDO MST EL EF ELY EC EP HLO HLO2 Husp Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (Hsp : l_ACEIL (lay Σ2) + 0x10000 <= usp) by (rewrite ELY; clear - HLO HLO2; lia).
destruct (Z_le_gt_dec (X16j.qbytes (ql Σ2)) 0x100000) as [HBY|HBY].
-
assert (W1 : forall ms, enq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms ->
evt bsegs (fun ms' => exists (w1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m' : mem),
ms' = rl_ret_st usp gp s0 w1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F fc m'
/\ ART_A Σ2 m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -2128)
/\ rt_pres (live Σ2) (frames Σ) usp m m' /\ icpt_frame m' usp ra s0 s1 s2 s3 s4 s5) ms).
{ intros ms P. destruct P as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
& w1 & m5 & -> & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5).
pose proof (geo_of_wfx Σ2 WX5) as HG2.
eapply evt_mono; [apply (ret_tail Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
t3 t4 t5 t6 w1 _ _ F fc m5 lo HG2 ART5 WX5 WC5 HBY MI5 ST5 ltac:(rewrite ELY; exact HLO)
HLO2 Husp FR5)|].
intros ms' P'. destruct P' as (w1' & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m' & -> & ART' & MI' & WM' & ST' & MU').
exists w1', z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m'. split; [reflexivity|].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|].
split.
{ intros a Ha. rewrite (MU' a); [exact (RP5 a Ha)|].
pose proof (ART_wf Σ2 m' ART') as HW2. pose proof HW2 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
pose proof (aclient_split Σ2 (live Σ2) usp (bv_unsigned a) HG2 Hsp
ltac:(intros p0 n0 Hin; destruct (V3 p0 n0 Hin) as [X|(s & Hs & Hq & Hsn & ->)]; [left; exact X|];
right; destruct (In_nth_error _ _ Hs) as (k & Hk'); exists k, s; split; [exact Hk' | split; [exact Hq | split; [exact Hsn | reflexivity]]])
ltac:(rewrite EF; exact Ha)) as HO.
cbn [outside] in HO |- *. clear - HO Hsp. split; [lia | exact I]. }
apply (icpt_frame_transport _ m5 m' usp ra s0 s1 s2 s3 s4 s5 ICF5 MU' WM'). cbn [disjoint_from]. split; [clear; lia | exact I]. }
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ2) _ _ _ (fl_ASTA_mat_stable Σ2 PMc MST) W1) Hc).
intros c1 Hc1. apply Hk.
exists Σ2. split; [|split; [exact EL | split; [exact EF | split; [exact ELY | exact (conj EC EP)]]]].
unfold ASTA. eapply AST_conseq; [exact Hc1| |intros mo H; exact H].
intros ms (w1 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & ART' & MI' & ST' & RP' & ICF').
exists w1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m'. split; [reflexivity|].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite <- EL; exact RP' | exact ICF'].
-
destruct Hc as (Hmc & HP & HPM & HZ).
destruct HP as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
& w1 & m5 & E5 & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5).
assert (Hc' : ASTA RTA Σ2 PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ2) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4a234) fc None m5 (seg_rom bsegs))) cf).
{ split; [exact Hmc|]. split; [unfold enq_ret_st in E5; exact (eq_sym E5)|]. split; [exact HPM | exact HZ]. }
apply (DRAIN Σ2 PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5 lo usp
s0 w1 s2 s3 s4 s5 s6 FDO MST ART5 WX5 WC5 ltac:(clear - HBY; lia) FR5 ST5 ltac:(rewrite ELY; exact HLO) ltac:(clear - HLO2; lia)
ltac:(clear - Husp; unfold USTACK_TOP in *; lia) MI5 T cf Hc').
intros c2 (Σ' & Hc2 & EL' & EF' & ELY' & EC' & EP'). apply Hk.
exists Σ'. split; [|split; [exact (eq_trans EL' EL) | split; [exact (eq_trans EF' EF) | split; [exact (eq_trans ELY' ELY) | exact (conj (eq_trans EC' EC) (eq_trans EP' EP))]]]].
unfold ASTA in *. eapply AST_conseq; [exact Hc2| |intros mo H; exact H].
intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & ART6 & MI6 & ST6 & RP6).
exists w1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m6. split; [reflexivity|].
split; [exact ART6|]. split; [exact MI6|]. split; [exact ST6|].
assert (AG : forall a : word, usp - 2128 <= bv_unsigned a < usp -> m6 a = m5 a).
{ intros a Ha. apply RP6. left. clear - Ha Husp. unfold USTACK_TOP in *. lia. }
split; [|exact (icpt_frame_agree m5 m6 usp ra s0 s1 s2 s3 s4 s5 ICF5 AG)].
intros a Ha. rewrite (RP6 a) by (rewrite EL, EF; destruct Ha as [Ha|Ha]; [left; unfold USTACK_TOP in *; lia | right; exact Ha]).
exact (RP5 a ltac:(rewrite EL; exact Ha)).
Qed.

End Fin.
End RL_FH.
Export RL_FH.

Module RL_freeV.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X18s X18k X16z X18d X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141 X143 X145 X14b X14i X14j.
Import RL_stmt RL_A2 RL_G RL_FH.

Section AppG.
Variables (Σ1 : rtsA) (M n : Z) (m : mem) (pre : list batch) (j0 : nat) (ents : list (Z * Z)) (usp : Z).
Hypothesis HW1 : rt_wf0 Σ1.
Hypothesis HP : pend_e Σ1 M n.
Hypothesis HQL : ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents)].
Hypothesis Hj0 : nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch.
Hypothesis HL : (length ents < 1021)%nat.
Hypothesis Hsp : l_ACEIL (lay Σ1) + 0x10000 <= usp.
#[local] Notation L := (lay Σ1).
#[local] Notation T := (l_T (lay Σ1)).
#[local] Notation SB := (l_SB (lay Σ1)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ1)) 24 j0).
#[local] Notation W := (W_E (l_T (lay Σ1)) (p_abeg (l_SB (lay Σ1)) 24 j0) (p_abeg (l_SB (lay Σ1)) 24 j0) usp).
#[local] Notation Wa := [(l_T (lay Σ1) + 80, l_T (lay Σ1) + 112); (p_abeg (l_SB (lay Σ1)) 24 j0, p_abeg (l_SB (lay Σ1)) 24 j0 + 8192); (usp - 2400, usp)].
#[local] Notation Σ2 := (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])).

Theorem app_ART_g : forall (m4 m' : mem) (ql' : list batch), ARTc Σ1 m4 -> munch Wa m4 m' -> wmono bsegs m4 m' ->
qcache_rep m' (qcacheT T) ql' -> ARTc (set_ql Σ1 ql') m'.
Proof using HW1 HQL Hj0 HL Hsp.
intros m4 m' ql' ART4 MU WM QT. pose proof (geo_of_wf0 Σ1 HW1) as HG. pose proof HW1 as (_ & _ & _ & _ & _ & _ & _ & Dok & _).
assert (MW : munch W m4 m') by (apply (munch_weaken Wa _ m4 m'); [unfold W_E; clear; solve_sub_fp | exact MU]).
pose proof (se_img Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWi. pose proof (se_Tz Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWt.
pose proof (se_grant Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWg. pose proof (se_ris Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWr.
pose proof (se_fa Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWf. pose proof (se_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWs.
pose proof (se_shad_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWss. pose proof (se_shad_reg Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWsr.
pose proof (se_shad_app Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWsa. pose proof (se_secmap Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWm.
destruct ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
pose proof (g_grant Σ1 HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
apply ARTc_intro; cbn [set_ql lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 ia_init credit live frames fsc] in *.
-
apply (consts_rep_frame L m4 m' CR); [|exact WM]. intros a Ha. apply MW.
destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
+ rewrite E. unfold W_E. cbn [outside]. pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (_ & _ & _ & K4 & K5 & K6 & K7 & K8 & _ & _ & K11 & K12 & _ & K14 & _).
pose proof (se_disj Σ1 HG) as (_ & _ & ATP). clear - K4 K5 K6 K7 K8 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
+ apply (kv_consts Σ1 W (TZ_E T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_E; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
-
intros c' Hc'. pose proof (PR c' Hc') as X. cbn [pr lay set_ql] in X |- *.
exact (reg_rep_transport W _ c' _ m4 m' X MW WM (kv_reg Σ1 W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0) (fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c' Hc' ltac:(intros []))).
-
intros c' Hc'. pose proof (CA c' Hc') as X. cbn [lay pr ca ca_init set_ql] in X |- *. destruct (Z.eq_dec c' 24) as [->|Hcc].
+ apply (pclass_rep_transport Wa _ 24 _ _ m4 m' X MU WM). unfold pclass_avoid, pc_addr, cacheT. cbn [disjoint_from].
pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (_ & _ & _ & K4 & K5 & K6 & K7 & K8 & _ & _ & K11 & K12 & _ & K14 & _).
pose proof (se_disj Σ1 HG) as (_ & _ & ATP). clear - K4 K5 K6 K7 K8 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
split; [lia|]. split; [lia|]. split; [lia | exact I].
+ apply (pclass_rep_transport W _ c' _ _ m4 m' X MW WM). apply (kv_pclass Σ1 W (TZ_E T) HWt c' Hc').
unfold TZ_E, pc_addr, cacheT. cbn [disjoint_from]. clear - Hc' Hcc. repeat split; try exact I; lia.
-
destruct CH as [P Sc]. split.
+ intros c' i' st Hc' Hn'. pose proof (P c' i' st Hc' Hn') as X. cbn [lay pr set_ql] in X, Hn' |- *. pose proof Hn' as Hn0.
{ assert (HD : (c' = 24 /\ i' = j0) \/ ~ In (c', i') [(24, j0); (24, j0)]).
{ destruct (Z.eq_dec c' 24) as [->|X1]; [destruct (Nat.eq_dec i' j0) as [->|X2]; [left; split; reflexivity|]|].
- right. intros Hin. apply X2. destruct Hin as [E|[E|[]]]; injection E; auto.
- right. intros Hin. apply X1. destruct Hin as [E|[E|[]]]; injection E; auto. }
destruct HD as [(-> & ->)|Hnin].
--
rewrite Hj0 in Hn0. injection Hn0 as <-. apply (pchunk_transport W _ 24 j0 _ m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp j0 CkBatch Hj0).
-- apply (pchunk_transport W _ c' i' _ m4 m' X MW WM). exact (kv_pchunk Σ1 W _ HG HWs HWss c' i' st Hc' Hn0 Hnin). }
+ intros k s Hk. apply (schunk_transport W k s m4 m' (Sc k s Hk) MW WM). exact (kv_schunk Σ1 W [] HG HWsa HWm k s Hk ltac:(intros [])).
-
exact (sec_rep_transport W _ m4 m' SR MW WM (kv_sec Σ1 W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
-
destruct QR as (_ & (QG & CG) & MX). split; [exact QT|]. split.
+ split; [apply (rw_cells_transport bsegs W m4 m' _ _ QG MW WM); cbn [cells_size csize Nat.add]; apply HWi; [unfold i_q_global, INST, g_instance; lia | unfold i_q_global, INST, g_instance, SEGTOP_A; lia | exact I]|].
apply (qchain_transport W m4 m' _ CG MW WM). pose proof HW1 as (_ & _ & _ & _ & (_ & _ & QB & QN & _) & _).
apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) QB b ltac:(apply in_or_app; right; exact Hb)) as (j & Hj & Eb). rewrite Eb.
assert (Hjne : j <> j0).
{ intros ->. rewrite HQL in QN. rewrite <- app_assoc, map_app in QN. cbn [app map fst] in QN. apply NoDup_ListNoDup in QN.
apply (NoDup_remove_2 (map fst pre) (map fst (qg Σ1)) b0 QN). apply in_or_app. right. rewrite <- Eb. apply in_map. exact Hb. }
apply (HWs 24 j CkBatch); [lia | exact Hj | intros [E|[E|[]]]; injection E as E; exact (Hjne (eq_sym E)) | lia | change (ClassSize 24) with 8192; lia].
+ apply (rw_cells_transport bsegs W m4 m' _ _ MX MW WM). cbn [cells_size csize Nat.add].
apply HWi; [unfold i_q_cmutex, INST, g_instance; lia | unfold i_q_cmutex, INST, g_instance, SEGTOP_A; lia | exact I].
-
exact (dep_rep_transport W L (dep Σ1) m4 m' DR Dok MW WM (kv_dep Σ1 W [] HWi ltac:(apply Forall_forall; intros; exact I)
(se_grant67 Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp))).
-
exact (fs_rep_transport W _ m4 m' FR MW WM (kv_fs Σ1 W [] (TZ_E T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
ltac:(unfold TZ_E; cbn; repeat split; try exact I; lia))).
- exact (ia_rep_transport W _ m4 m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
- exact (shadow_rep_transport W _ _ m4 m' SHR MW WM (kv_shadow Σ1 W [] HG HWsa)).
- exact (vis_rep_wmono _ m4 m' VIS WM).
Qed.

Lemma app_enq_g : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
(F : bvmap 5 word) (fc : bv 32) (m4 : mem) (lo : Z),
bv_unsigned sp = usp -> ARTc Σ1 m4 -> mem_inv bsegs m4 -> wmono bsegs m m4 ->
stk bsegs m4 lo (usp + -2208) -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
rt_pres (live Σ1) (frames Σ1) usp m m4 ->
icpt_frame m4 usp ra s0 s1 s2 s3 s4 s5 ->
qput_frame m4 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) s0
(Z_to_bv 64 (M + 16)) s2 s3 s4 s5 s6 ->
evt bsegs (enq_post Σ2 (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 M) (Z_to_bv 64 n) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m4 (seg_rom bsegs)).
Proof using HW1 HP HQL Hj0 HL Hsp.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
Esp ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4.
pose proof (geo_of_wf0 Σ1 HW1) as HG.
pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (se_disj Σ1 HG) as (T5 & T4 & ATP).
assert (Hn1 : 1 <= n <= 2 ^ 27) by (pose proof HP as (QE & _); exact (pe_n Σ1 M n HW1 QE)).
assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
pose proof (qwf_ql Σ1 HW1) as QWF. rewrite HQL in QWF.
pose proof HW1 as (_ & _ & _ & _ & (Q1 & _) & _).
pose proof ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
pose proof QR as (QT & _). cbn [ql lay] in QT. rewrite HQL in QT.
rewrite HQL, <- qbytes_eq in Q1.
eapply evt_mono.
{ apply (qenq_app_spec (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4
(T + 80) (T + 208) (usp + -2056) M n SB lo pre b0 ents);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
all: try (clear - Hn1; lia).
all: try exact ST4.
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - K13; lia). all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
eapply Z.le_lt_trans; [apply Z.add_le_mono; [exact Q1 | exact (proj2 Hn1)] | reflexivity]. }
intros ms5 P5. destruct P5 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m5 & -> & MU5 & WM5 & MI5 & QR5 & _ & ST5).
rewrite (unsigned_lit (usp + -2208)) in MU5, ST5 by exact RSP. rewrite (ret_pc_even 0x4a234) by (first [reflexivity | lia]).
assert (MWa : munch [(T + 80, T + 112); (b0, b0 + 8192); (usp - 2400, usp)] m4 m5).
{ lazymatch type of MU5 with munch ?W5 _ _ => apply (munch_weaken W5 _ m4 m5); [clear - Hsp; solve_sub_fp | exact MU5] end. }
unfold enq_post. exists (Z_to_bv 64 0x4a234), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2056)),
(Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 (M + 16)), m5.
split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
split; [exact (app_ART_g m4 m5 _ ART4 MWa WM5 QR5)|].
destruct (app_wfx_e Σ1 M n pre j0 ents HW1 HP HQL HL) as (WX & WC).
split; [exact WX|]. split; [exact WC|]. split; [exact MI5|]. split; [exact (wmono_trans bsegs _ _ _ WM4 WM5)|].
split; [rewrite Esp; exact ST5|].
split.
{ rewrite Esp. intros a Ha. rewrite (MWa a); [exact (RP4 a Ha)|].
assert (HO : outside (W_E (l_T (lay Σ1)) b0 b0 usp) (bv_unsigned a)).
{ apply (kv_client Σ1 _ [(24, j0); (24, j0)] [] [] usp HG
(se_img Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_grant Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
(se_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_shad_app Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
(se_secmap Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_stack Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
ltac:(apply Forall_forall; intros; exact I) (live Σ1)); [|exact Ha].
intros p' n' Hin.
pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
intros [E|[E|[]]]; injection E as <- <-; rewrite Hj0 in Hn'; discriminate.
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
revert HO. apply sub_fp_covered. unfold W_E. cbn [all_covered covered]. clear - Hsp.
split; [left; split; lia|]. split; [right; right; right; left; split; lia|]. split; [right; right; right; right; right; left; split; lia | exact I]. }
split.
{ rewrite Esp. apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). cbn [disjoint_from].
clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
rewrite Esp. unfold qput_frame in FR4 |- *. apply (rw_cells_transport bsegs _ m4 m5 _ _ FR4 MU5 WM5).
cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End AppG.
End RL_freeV.
Export RL_freeV.

Module RL_freeW.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X18s X18k X18o X18l X16z X18d X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141 X143 X145 X146 X148 X14b X14i X14j.
Import RL_stmt RL_A2 RL_G RL_FH RL_freeV.

Section NewG2.
Variables (Σ : rtsA) (M n : Z) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σ)) 24 j0) (map fst (ql Σ))).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Theorem new_ART_g : forall (m4 m' : mem), ARTc Σ m4 -> munch W m4 m' -> wmono bsegs m4 m' ->
qcache_rep m' (qcacheT T) (ql Σ ++ [(bB, [(M, n)])]) -> pclass_rep T 24 (ca_init Σ) cal m' -> ARTc (enq_new Σ cal jB M n) m'.
Proof using HW0 HCA Hj0 Hvar Hsp.
intros m4 m' ART4 MW WM QT PC24.
pose proof (ng_geo Σ HW0) as HG. pose proof (ng_jB Σ cal jB HW0 HCA) as HjB.
pose proof (se_img Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWi. pose proof (se_Tz Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWt.
pose proof (se_grant Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWg. pose proof (se_ris Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWr.
pose proof (se_fa Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWf. pose proof (se_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWs.
pose proof (se_shad_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWss. pose proof (se_shad_reg Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWsr.
pose proof (se_shad_app Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWsa. pose proof (se_secmap Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWm.
pose proof (se_geo Σ j0 jB st0 CkIdle HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
assert (RA : forall c', 1 <= c' <= 31 -> reg_avoid W SB c' (pr Σ c')).
{ intros c' Hc'. exact (kv_reg Σ W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0)
(fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c' Hc' ltac:(intros [])). }
destruct ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
apply ARTc_intro.
-
cbn [enq_new pop24 set_ql lay] in *.
apply (consts_rep_frame L m4 m' CR); [|exact WM]. intros a Ha. apply MW.
destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
+ rewrite E. unfold W_E. cbn [outside]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
+ apply (kv_consts Σ W (TZ_E T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_E; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
-
intros c' Hc'. pose proof (PR c' Hc') as X. cbn [enq_new pop24 set_ql lay pr] in X |- *.
destruct (Z.eqb_spec c' 24) as [->|Hcc].
+ exact (reg_rep_transport W _ 24 _ m4 m' (reg_rep_upd _ _ _ jB CkBatch m4 X) MW WM (reg_avoid_upd _ _ _ _ _ _ (RA 24 ltac:(lia)))).
+ exact (reg_rep_transport W _ c' _ m4 m' X MW WM (RA c' Hc')).
-
intros c' Hc'. pose proof (CA c' Hc') as X. cbn [enq_new pop24 set_ql lay pr ca ca_init] in X |- *.
destruct (Z.eqb_spec c' 24) as [->|Hcc]; [exact PC24|].
apply (pclass_rep_transport W _ c' _ _ m4 m' X MW WM). apply (kv_pclass Σ W (TZ_E T) HWt c' Hc').
unfold TZ_E, pc_addr, cacheT. cbn [disjoint_from]. clear - Hc' Hcc. repeat split; try exact I; lia.
-
destruct CH as [P Sc]. split.
+ intros c' i' st Hc' Hn'. cbn [enq_new set_ql lay] in Hn' |- *.
destruct (pop24_st Σ cal jB c' i' st Hn') as [(-> & -> & ->)|(Hne & Hn1)].
*
pose proof (P 24 jB CkIdle ltac:(lia) HjB) as X.
cbn [lay pchunk] in X |- *. destruct X as (_ & X).
apply (pchunk_transport W _ 24 jB CkBatch m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp jB CkIdle HjB).
* pose proof (P c' i' st Hc' Hn1) as X. cbn [lay] in X, Hn1 |- *.
assert (HD : (c' = 24 /\ i' = j0) \/ ~ In (c', i') [(24, j0); (24, jB)]).
{ destruct (Z.eq_dec c' 24) as [->|X1]; [destruct (Nat.eq_dec i' j0) as [->|X2]; [left; split; reflexivity|]|].
- right. intros Hin. destruct Hin as [E|[E|[]]]; injection E as E; [exact (X2 (eq_sym E))|].
destruct Hne as [Y|Y]; [exact (Y eq_refl) | exact (Y (eq_sym E))].
- right. intros Hin. apply X1. destruct Hin as [E|[E|[]]]; injection E; auto. }
destruct HD as [(-> & ->)|Hnin].
--
rewrite Hj0 in Hn1. injection Hn1 as Est. destruct Hvar as [(E & _)|(E0 & _)]; [destruct Hne as [Y|Y]; [exfalso; exact (Y eq_refl) | exfalso; exact (Y E)]|].
rewrite <- Est, E0 in X |- *.
apply (pchunk_transport W _ 24 j0 _ m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp j0 st0 Hj0).
-- apply (pchunk_transport W _ c' i' _ m4 m' X MW WM). exact (kv_pchunk Σ W _ HG HWs HWss c' i' st Hc' Hn1 Hnin).
+ intros k s Hk. cbn [enq_new pop24 set_ql sec] in Hk |- *.
apply (schunk_transport W k s m4 m' (Sc k s Hk) MW WM). exact (kv_schunk Σ W [] HG HWsa HWm k s Hk ltac:(intros [])).
-
cbn [enq_new pop24 set_ql] in *.
exact (sec_rep_transport W _ m4 m' SR MW WM (kv_sec Σ W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
-
cbn [enq_new pop24 set_ql ql qg lay] in *.
destruct QR as (_ & (QG & CG) & MX). split; [exact QT|]. split.
+ split; [apply (rw_cells_transport bsegs W m4 m' _ _ QG MW WM); cbn [cells_size csize Nat.add]; apply HWi; [unfold i_q_global, INST, g_instance; lia | unfold i_q_global, INST, g_instance, SEGTOP_A; lia | exact I]|].
apply (qchain_transport W m4 m' _ CG MW WM). pose proof HW0 as (_ & _ & _ & _ & (_ & _ & QB & QN & _) & _).
apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) QB b ltac:(apply in_or_app; right; exact Hb)) as (j & Hj & Eb). rewrite Eb.
assert (HjjB : j <> jB) by (intros ->; rewrite HjB in Hj; discriminate Hj).
assert (Hjj0 : j <> j0).
{ intros ->. destruct Hvar as [(E & _)|(_ & Hin)]; [exact (HjjB E)|].
rewrite map_app in QN. apply NoDup_ListNoDup in QN. apply (fl_nodup_app_not_in _ _ _ QN Hin). rewrite <- Eb. apply in_map. exact Hb. }
apply (HWs 24 j CkBatch); [lia | exact Hj | | lia | change (ClassSize 24) with 8192; lia].
intros [E|[E|[]]]; injection E as E; [exact (Hjj0 (eq_sym E)) | exact (HjjB (eq_sym E))].
+ apply (rw_cells_transport bsegs W m4 m' _ _ MX MW WM). cbn [cells_size csize Nat.add].
apply HWi; [unfold i_q_cmutex, INST, g_instance; lia | unfold i_q_cmutex, INST, g_instance, SEGTOP_A; lia | exact I].
-
cbn [enq_new pop24 set_ql lay dep] in *. pose proof HW0 as (_ & _ & _ & _ & _ & _ & _ & Dok & _).
exact (dep_rep_transport W L (dep Σ) m4 m' DR Dok MW WM (kv_dep Σ W [] HWi ltac:(apply Forall_forall; intros; exact I)
(se_grant67 Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp))).
-
cbn [enq_new pop24 set_ql] in *.
exact (fs_rep_transport W _ m4 m' FR MW WM (kv_fs Σ W [] (TZ_E T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
ltac:(unfold TZ_E; cbn; repeat split; try exact I; lia))).
- cbn [enq_new pop24 set_ql] in *. exact (ia_rep_transport W _ m4 m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
- cbn [enq_new pop24 set_ql lay] in *. exact (shadow_rep_transport W _ _ m4 m' SHR MW WM (kv_shadow Σ W [] HG HWsa)).
- exact (vis_rep_wmono _ m4 m' VIS WM).
Qed.

End NewG2.

Section NewE.
Variables (Σ : rtsA) (M n : Z) (m : mem) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis HP : pend_e Σ M n.
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
\/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation Σ1 := Σ.
#[local] Notation Σ2 := (enq_new Σ cal jB M n).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Lemma new_enq_g : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
(F : bvmap 5 word) (fc : bv 32) (m4 : mem) (lo : Z),
bv_unsigned sp = usp -> ARTc Σ1 m4 -> mem_inv bsegs m4 -> wmono bsegs m m4 ->
stk bsegs m4 lo (usp + -2208) -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
rt_pres (live Σ) (frames Σ) usp m m4 ->
icpt_frame m4 usp ra s0 s1 s2 s3 s4 s5 ->
qput_frame m4 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) s0
(Z_to_bv 64 (M + 16)) s2 s3 s4 s5 s6 ->
evt bsegs (enq_post Σ2 (live Σ) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 M) (Z_to_bv 64 n) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m4 (seg_rom bsegs)).
Proof using HW0 HP HCA Hj0 Hvar Hsp.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
Esp ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4.
pose proof (geo_of_wf0 Σ HW0) as HG.
pose proof (ng_jB Σ cal jB HW0 HCA) as HjB.
pose proof (se_geo Σ j0 jB st0 CkIdle HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
pose proof (g_grant Σ HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
pose proof (g_prb Σ HG) as (P1 & P2 & P3).
assert (Hn1 : 1 <= n <= 2 ^ 27) by (pose proof HP as (QE & _); exact (pe_n Σ M n HW0 QE)).
assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
pose proof ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).

destruct (new_wfx_e Σ cal jB M n HW0 HP HCA) as (WX & WC).
pose proof (qwf_ql_x _ WX) as QWF. cbn [enq_new set_ql ql pop24 lay free_p] in QWF.
pose proof HW0 as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq in Q1.

assert (Hinit : ca_init Σ = true).
{ destruct (ca_init Σ) eqn:E; [reflexivity|]. pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & _ & R4 & _).
rewrite (R4 E 24) in HCA. destruct cal; discriminate HCA. }
assert (Hcnt : 1 <= Z.of_nat (length (cal ++ [Z.of_nat jB])) <= 16).
{ pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & R3 & _). destruct (R3 24 ltac:(lia)) as (C1 & _). rewrite HCA in C1.
pose proof (MaxCount_range 24 ltac:(lia)) as (MC & _). rewrite length_app in C1 |- *. cbn [length] in C1 |- *. clear - C1 MC. lia. }
pose proof (CA 24 ltac:(lia)) as PC. cbn [ca ca_init free_p lay] in PC. rewrite HCA, Hinit in PC. destruct PC as (PCC & chs & ARR & Hlen & Hpre).
change (ClassSize 24) with 8192 in PCC.
assert (Hw : nth_error chs (Z.to_nat (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1)) = Some (cpw 24 (Z.of_nat jB))).
{ pose proof (fl_hit_w (cpw 24) (cal ++ [Z.of_nat jB]) chs ltac:(destruct cal; discriminate) Hpre) as X. rewrite last_last in X.
replace (Z.to_nat (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1)) with (length (cal ++ [Z.of_nat jB]) - 1)%nat by (clear; rewrite length_app; cbn [length]; lia).
exact X. }
assert (HAB : chunk_addr SB 24 (cpw 24 (Z.of_nat jB)) = bB).
{ rewrite fl_hit_addr; [rewrite Nat2Z.id; reflexivity | lia | | reflexivity]. change (ClassSize 24) with 8192. clear - K9 K10. unfold p_abeg, rb, kUserCap in *.
change (ClassSize 24) with 8192 in *. lia. }
pose proof (MaxCount_range 24 ltac:(lia)) as (MC1 & _).

assert (NC : exists stj jb, qnew_cells m4 T SB (Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb).
{ destruct CR as (CI & _ & _ & _ & _ & _ & _ & ICR). pose proof ICR as STS. do 31 (apply proj2 in STS). apply proj1 in STS.
cbn [lay free_p] in STS. destruct (stk_split bsegs m4 (T + 2768) (T + 2784) (T + 3168) STS ltac:(lia)) as [_ STS1].
destruct (stk_split bsegs m4 (T + 2784) (T + 2784 + 8) (T + 3168) STS1 ltac:(lia)) as [STS2 _].
destruct (fl_c8_of_stk m4 (T + 2784) STS2) as (stj & HST).
destruct CH as (P & _). pose proof (P 24 jB CkIdle ltac:(lia) HjB) as PB.
cbn [pchunk lay free_p] in PB. destruct PB as (PB & _). change (ClassSize 24) with 8192 in PB.
destruct (fl_CB_of_stk m4 bB 8192 PB) as (jb & HJB).
exists stj, jb. unfold qnew_cells. split; [exact PCC|]. split; [exact ARR|]. split; [exact HST|].
split; [cbn [lay free_p] in CI; destruct CI as (CI & _); exact (proj1 (proj1 (rwc_app bsegs m4 i_spacebeg [C8 (Z_to_bv 64 SB)] _) CI))|].
rewrite HAB. exact HJB. }
destruct NC as (stj & jb & NC).

eapply (evt_mono bsegs (qenq_post (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 F fc
[(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
(b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] (qcacheT T) (ql Σ ++ [(bB, [(M, n)])]) lo m4
(fun m' => qnew_after m' T SB (Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs))).
{ destruct Hvar as [(E1 & E2 & HQL)|(E1 & pre & ents0 & HQL & HL0)].
- pose proof QR as (QT & _). cbn [ql lay free_p] in QT. rewrite HQL in QT.
eapply evt_mono.
{ apply (qenq_new_hit_empty_spec (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4 T (usp + -2056) M n SB lo
(Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
all: try (clear - Hn1; lia). all: try (clear - MC1; lia).
all: try (clear - P3; unfold p_abeg; apply Z.mod_divide in P3; [|lia]; destruct P3 as [q Hq]; rewrite Hq;
replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat jB * ClassSize 24) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat jB) * 8192)
by (change (ClassSize 24) with 8192; ring); apply Z.mod_mul; lia).
all: try (clear - K9 K10; unfold r24, rb, kUserCap in *; lia).
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try exact ST4.
all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL.
eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp.
- pose proof QR as (QT & _). cbn [ql lay free_p] in QT. rewrite HQL in QT. rewrite HQL in QWF, Q1.
rewrite <- app_assoc in QWF. cbn [app] in QWF.
eapply evt_mono.
{ apply (qenq_new_hit_full_spec (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4 T (usp + -2056) M n SB lo
(Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb pre b0 ents0);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
all: try (clear - Hn1; lia). all: try (clear - MC1; lia).
all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try exact ST4. all: try exact QWF.
all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL, <- app_assoc. cbn [app].
eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp. }
intros ms5 P5. destruct P5 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m5 & -> & MU5 & WM5 & MI5 & QR5 & NA5 & ST5).
rewrite (ret_pc_even 0x4a234) by (first [reflexivity | lia]).
destruct NA5 as (NA1 & NA2 & _).
assert (HSUB : sub_fp [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
(b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] W).
{ clear - Hsp. unfold W_E, qcacheT, pc_addr, cstat_alloc. solve_sub_fp. }
assert (PC5 : pclass_rep T 24 (ca_init Σ) cal m5).
{ rewrite Hinit. split.
- replace (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1) with (Z.of_nat (length cal)) in NA1 by (clear; rewrite length_app; cbn [length]; lia).
change (ClassSize 24) with 8192. exact NA1.
- exists chs. split; [exact NA2|]. split; [exact Hlen|]. exact (firstn_snoc_map (cpw 24) cal (Z.of_nat jB) chs Hpre). }
assert (Hvar' : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In b0 (map fst (ql Σ)))).
{ destruct Hvar as [(E1 & E2 & _)|(E1 & pre & ents0 & HQL & _)]; [left; split; assumption|]. right. split; [exact E1|].
rewrite HQL, map_app. apply in_or_app. right. left. reflexivity. }
unfold enq_post. exists (Z_to_bv 64 0x4a234), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2056)),
(Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 (M + 16)), m5.
split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
split; [exact (new_ART_g Σ M n cal jB j0 st0 usp HW0 HCA Hj0 Hvar' Hsp m4 m5 ART4 (munch_weaken _ _ _ _ HSUB MU5) WM5 QR5 PC5)|].
split; [exact WX|]. split; [exact WC|]. split; [exact MI5|]. split; [exact (wmono_trans bsegs _ _ _ WM4 WM5)|].
split; [rewrite Esp; rewrite (unsigned_lit (usp + -2208)) in ST5 by exact RSP; exact ST5|].
split.
{ rewrite Esp. intros a Ha. rewrite (MU5 a); [exact (RP4 a Ha)|]. apply HSUB.
apply (kv_client Σ _ [(24, j0); (24, jB)] [] [] usp HG
(se_img Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_grant Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
(se_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_shad_app Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
(se_secmap Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_stack Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
ltac:(apply Forall_forall; intros; exact I) (live Σ)); [|exact Ha].
intros p' n' Hin.
pose proof HW0 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
intros [E|[E|[]]]; injection E as <- <-; [rewrite Hj0 in Hn'; injection Hn' as Est; destruct Hvar' as [(_ & X)|(X & _)]; rewrite X in Est; discriminate Est
| rewrite HjB in Hn'; discriminate Hn'].
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
split.
{ rewrite Esp. apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from].
clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
rewrite Esp. unfold qput_frame in FR4 |- *. apply (rw_cells_transport bsegs _ m4 m5 _ _ FR4 MU5 WM5).
unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End NewE.
End RL_freeW.
Export RL_freeW.

Module RL_freeX.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X18s X18k X18o X18l X18m X18n X16z X18d X18z X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141 X143 X140 X144 X145 X146 X147 X148 X149 X14b X14i X14j X15y X15x X15z X163 X12s.
Import RL_stmt RL_A2 RL_G RL_FH RL_freeV RL_freeW.

Section MissG.
Variables (Σ1 : rtsA) (M n : Z) (m : mem) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW1 : rt_wf0 Σ1.
Hypothesis HP : pend_e Σ1 M n.
Hypothesis HCA0 : ca Σ1 24 = [].
Hypothesis Hsp : l_ACEIL (lay Σ1) + 0x10000 <= usp.
#[local] Notation L := (lay Σ1).
#[local] Notation T := (l_T (lay Σ1)).
#[local] Notation SB := (l_SB (lay Σ1)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ1)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ1)) 24 jB).
#[local] Notation Σb := (refillΣ Σ1 24).
#[local] Notation Σ2 := (enq_new (refillΣ Σ1 24) [] jB M n).
#[local] Notation W := (W_E (l_T (lay Σ1)) (p_abeg (l_SB (lay Σ1)) 24 j0) (p_abeg (l_SB (lay Σ1)) 24 jB) usp).
Hypothesis HjB : refill_ca (pr Σ1 24) 24 = [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σb 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle /\ ql Σ1 = [])
\/ (st0 = CkBatch /\ exists pre ents0, ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents0)] /\ length ents0 = 1021%nat).

Lemma mx_room : refill_room Σ1 24.
Proof using HW1 HP HCA0. exact (pend_room_e Σ1 M n HW1 HP HCA0). Qed.

Lemma mx_wfb : rt_wf0 Σb.
Proof using HW1 HP HCA0. exact (refill_wf0 Σ1 24 ltac:(clear; lia) HW1 HCA0 mx_room). Qed.

Lemma mx_pendb : pend_e Σb M n.
Proof using HW1 HP. exact (pend_refill_e Σ1 M n HW1 HP). Qed.

Lemma mx_cab : ca Σb 24 = [] ++ [Z.of_nat jB].
Proof using HjB. cbn [refillΣ ca]. rewrite Z.eqb_refl. exact HjB. Qed.

Lemma mx_var : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σb)) 24 j0) (map fst (ql Σb))).
Proof using Hvar.
destruct Hvar as [(E1 & E2 & _)|(E1 & pre & ents0 & HQL & _)]; [left; split; assumption|]. right. split; [exact E1|].
cbn [refillΣ ql lay]. rewrite HQL, map_app. apply in_or_app. right. left. reflexivity.
Qed.

Lemma mx_rt_eager : rt_eager Σ2 = rt_eager Σb.
Proof.
apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
cbn [enq_new set_ql pop24 pr]. destruct (Z.eqb_spec k' 24) as [->|_]; [|split; reflexivity]. unfold upd_reg. cbn [r_muser r_mfa]. split; reflexivity.
Qed.

Lemma miss_enq_g : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m5 m6 : mem) (lo : Z) (jf : list byte) (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
bv_unsigned sp = usp -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
wmono bsegs m m5 -> rt_pres (live Σ1) (frames Σ1) usp m m5 ->
icpt_frame m5 usp ra s0 s1 s2 s3 s4 s5 ->
qput_frame m5 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46800) s0
(Z_to_bv 64 (M + 16)) s2 s3 s4 s5 s6 ->
rw_cells bsegs m5 (usp + -2208 + -64) [CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (T + 208)); C8 (Z_to_bv 64 (usp + -2056));
C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (T + 80)); C8 (Z_to_bv 64 QUAR); C8 (Z_to_bv 64 0x4a234)] ->
ARTc Σb m6 -> mem_inv bsegs m6 -> wmono bsegs m5 m6 -> stk bsegs m6 lo (usp + -2208 + -64) ->
munch (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) m5 m6 ->
evt bsegs (enq_post Σ2 (live Σ2) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra0 (Z_to_bv 64 (usp + -2208 + -64)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (pc_addr T 24)) (Z_to_bv 64 (cacheT T))
(Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 M) (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 n)
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 qenq_refill_ret) fc None m6 (seg_rom bsegs)).
Proof using HW1 HP HCA0 Hsp HjB Hj0 Hvar.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m5 m6 lo jf ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
Esp HLO HLO2 Husp WM5 RP5 ICF FR5 EF5 ART6 MI6 WM6 ST6 MU6.
pose proof mx_wfb as HWb. pose proof mx_pendb as HPb. pose proof mx_cab as HCA. pose proof mx_var as Hvar'.
pose proof (geo_of_wf0 Σb HWb) as HG. pose proof (geo_of_wf0 Σ1 HW1) as HG1.
pose proof (ng_jB Σb [] jB HWb HCA) as HjB'.
change (lay Σb) with (lay Σ1) in *.
pose proof (se_geo Σb j0 jB st0 CkIdle HG Hj0 HjB') as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (se_disj Σb HG) as (T5 & T4 & ATP).
pose proof (g_prb Σb HG) as (P1 & P2 & P3).
change (lay Σb) with (lay Σ1) in *.
assert (Hn1 : 1 <= n <= 2 ^ 27) by (pose proof HP as (QE & _); exact (pe_n Σ1 M n HW1 QE)).
assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).

assert (HWR : forall a k, usp + -2208 + -64 <= a -> a + k <= usp -> disjoint_from (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) a k).
{ intros a k H1 H2. pose proof (rz_geo Σ1 24 HG1 ltac:(lia)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
pose proof (rz_shad Σ1 24 HG1 ltac:(lia)) as (S1 & S2). pose proof (se_disj Σ1 HG1) as (Z5 & Z4 & ZTP).
cbn [lay free_p] in *. unfold W_R. cbn [disjoint_from]. clear - H1 H2 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 Y12 S1 S2 Hsp K14 K15 K4 K6.
unfold rb, kUserCap, rinfo, RIS_of, SHB in *. repeat split; try exact I; lia. }
assert (EF6 : rw_cells bsegs m6 (usp + -2208 + -64) [CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (T + 208)); C8 (Z_to_bv 64 (usp + -2056));
C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (T + 80)); C8 (Z_to_bv 64 QUAR); C8 (Z_to_bv 64 0x4a234)]).
{ apply (rw_cells_transport bsegs _ m5 m6 _ _ EF5 MU6 WM6). apply HWR; cbn [cells_size csize Nat.add]; clear - Hsp; lia. }
pose proof (g_grant Σb HG (l_T (lay Σ1)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
pose proof ART6 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).

destruct (new_wfx_e Σb [] jB M n HWb HPb HCA) as (WX & WC).
pose proof (qwf_ql_x _ WX) as QWF. cbn [enq_new set_ql ql pop24 lay refillΣ free_p] in QWF.
pose proof HWb as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq in Q1. cbn [refillΣ ql free_p] in Q1.

assert (Hinit : ca_init Σb = true) by reflexivity.
pose proof (CA 24 ltac:(lia)) as PC. cbn [ca ca_init lay] in PC. rewrite Hinit in PC. rewrite HCA in PC.
destruct PC as (PCC & chs & ARR & Hlen & Hpre).
change (ClassSize 24) with 8192 in PCC.
assert (Hw : nth_error chs (Z.to_nat (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1)) = Some (cpw 24 (Z.of_nat jB))).
{ pose proof (fl_hit_w (cpw 24) ([] ++ [Z.of_nat jB]) chs ltac:(discriminate) Hpre) as X. rewrite last_last in X.
replace (Z.to_nat (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1)) with (length ([] ++ [Z.of_nat jB]) - 1)%nat by (clear; cbn [length app]; lia).
exact X. }
assert (HAB : chunk_addr SB 24 (cpw 24 (Z.of_nat jB)) = bB).
{ rewrite fl_hit_addr; [rewrite Nat2Z.id; reflexivity | lia | | reflexivity]. change (ClassSize 24) with 8192. clear - K9 K10. unfold p_abeg, rb, kUserCap in *.
change (ClassSize 24) with 8192 in *. lia. }
pose proof (MaxCount_range 24 ltac:(lia)) as (MC1 & _).

assert (NC : exists stj jb, qnew_cells m6 T SB (Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb).
{ destruct CR as (CI & _ & _ & _ & _ & _ & _ & ICR). pose proof ICR as STS. do 31 (apply proj2 in STS). apply proj1 in STS.
cbn [lay] in STS. destruct (stk_split bsegs m6 (T + 2768) (T + 2784) (T + 3168) STS ltac:(lia)) as [_ STS1].
destruct (stk_split bsegs m6 (T + 2784) (T + 2784 + 8) (T + 3168) STS1 ltac:(lia)) as [STS2 _].
destruct (fl_c8_of_stk m6 (T + 2784) STS2) as (stj & HST).
destruct CH as (P & _). pose proof (P 24 jB CkIdle ltac:(lia) HjB') as PB.
cbn [pchunk lay] in PB. destruct PB as (PB & _). change (ClassSize 24) with 8192 in PB.
destruct (fl_CB_of_stk m6 bB 8192 PB) as (jb & HJB).
exists stj, jb. unfold qnew_cells. split; [exact PCC|]. split; [exact ARR|]. split; [exact HST|].
split; [cbn [lay] in CI; destruct CI as (CI & _); exact (proj1 (proj1 (rwc_app bsegs m6 i_spacebeg [C8 (Z_to_bv 64 SB)] _) CI))|].
rewrite HAB. exact HJB. }
destruct NC as (stj & jb & NC).

replace (usp + -2208 + -64) with (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -64) by (rewrite (unsigned_lit (usp + -2208)) by exact RSP; reflexivity).
eapply (evt_mono bsegs (qenq_post (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 F fc
[(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
(b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] (qcacheT T) (ql Σ1 ++ [(bB, [(M, n)])]) lo m6
(fun m' => qnew_after m' T SB (Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs))).
{ destruct Hvar as [(E1 & E2 & HQL)|(E1 & pre & ents0 & HQL & HL0)].
- pose proof QR as (QT & _). cbn [ql lay refillΣ free_p] in QT. rewrite HQL in QT.
eapply evt_mono.
{ apply (qenq_miss_B_empty_spec ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0x4a234) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) F fc m6 T (usp + -2056) M n SB lo
(Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb jf);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
all: try (clear - Hn1; lia). all: try (clear - MC1; lia). all: try (clear; cbn; lia).
all: try (clear - P3; unfold p_abeg; apply Z.mod_divide in P3; [|lia]; destruct P3 as [q Hq]; rewrite Hq;
replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat jB * ClassSize 24) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat jB) * 8192)
by (change (ClassSize 24) with 8192; ring); apply Z.mod_mul; lia).
all: try (clear - K9 K10; unfold r24, rb, kUserCap in *; lia).
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try exact ST6. all: try exact EF6.
all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL.
eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp.
- pose proof QR as (QT & _). cbn [ql lay refillΣ free_p] in QT. rewrite HQL in QT. rewrite HQL in QWF, Q1.
rewrite <- app_assoc in QWF. cbn [app] in QWF.
eapply evt_mono.
{ apply (qenq_miss_B_full_spec ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0x4a234) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) F fc m6 T (usp + -2056) M n SB lo
(Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb jf pre b0 ents0);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
all: try (clear - Hn1; lia). all: try (clear - MC1; lia). all: try (clear; cbn; lia).
all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try exact ST6. all: try exact QWF. all: try exact EF6.
all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL, <- app_assoc. cbn [app].
eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp. }
intros ms7 P7. destruct P7 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m7 & -> & MU7 & WM7 & MI7 & QR7 & NA7 & ST7).
rewrite (ret_pc_even 0x4a234) by (first [reflexivity | lia]).
destruct NA7 as (NA1 & NA2 & _).
assert (HSUB : sub_fp [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
(b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] W).
{ clear - Hsp. unfold W_E, qcacheT, pc_addr, cstat_alloc. solve_sub_fp. }
assert (PC7 : pclass_rep T 24 (ca_init Σb) [] m7).
{ rewrite Hinit. split.
- replace (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1) with (Z.of_nat (length (@nil Z))) in NA1 by (clear; cbn [length app]; lia).
change (ClassSize 24) with 8192. exact NA1.
- exists chs. split; [exact NA2|]. split; [exact Hlen|]. exact (firstn_snoc_map (cpw 24) [] (Z.of_nat jB) chs Hpre). }

assert (RP7 : rt_pres (live Σ2) (frames Σ1) usp m m7).
{ intros a Ha. rewrite (MU7 a).
- rewrite (MU6 a); [exact (RP5 a Ha)|].
assert (Hsp1 : l_ACEIL (lay Σ1) + 0x400 <= usp + -2208 + -64) by (cbn [lay free_p]; clear - Hsp; lia).
refine (kv_client Σ1 (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) [] [] []
(usp + -2208 + -64) HG1 (rz_img Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_grant Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_slot Σ1 24 _ HG1 ltac:(lia) Hsp1)
(rz_shad_app Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_secmap Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_stack Σ1 24 _ HG1 ltac:(lia) Hsp1)
ltac:(apply Forall_forall; intros; exact I) (live Σ1) _ _ _).
+ intros p' n' Hin. pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
* left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
* right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []].
+ destruct Ha as [X|X]; [left; clear - X Hsp; lia | right; exact X].
- apply HSUB.
apply (kv_client Σb _ [(24, j0); (24, jB)] [] [] usp HG
(se_img Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_grant Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
(se_slot Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_shad_app Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
(se_secmap Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_stack Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
ltac:(apply Forall_forall; intros; exact I) (live Σb)); [|exact Ha].
intros p' n' Hin. pose proof HWb as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
intros [E|[E|[]]]; injection E as <- <-; [rewrite Hj0 in Hn'; injection Hn' as Est; destruct Hvar' as [(_ & X)|(X & _)]; rewrite X in Est; discriminate Est
| rewrite HjB' in Hn'; discriminate Hn'].
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
unfold enq_post. exists (Z_to_bv 64 0x4a234), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2056)),
(Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 (M + 16)), m7.
split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
split; [exact (new_ART_g Σb M n [] jB j0 st0 usp HWb HCA Hj0 Hvar' Hsp m6 m7 ART6 (munch_weaken _ _ _ _ HSUB MU7) WM7 QR7 PC7)|].
split; [exact WX|]. split; [exact WC|]. split; [exact MI7|]. split; [exact (wmono_trans bsegs _ _ _ (wmono_trans bsegs _ _ _ WM5 WM6) WM7)|].
split; [rewrite Esp; rewrite (unsigned_lit (usp + -2208)) in ST7 by exact RSP; exact ST7|].
split; [rewrite Esp; exact RP7|].
split.
{ rewrite Esp. apply (icpt_frame_transport _ m6 m7 usp ra s0 s1 s2 s3 s4 s5 (icpt_frame_transport _ m5 m6 usp ra s0 s1 s2 s3 s4 s5 ICF MU6 WM6
ltac:(apply HWR; clear - Hsp; lia)) MU7 WM7). unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from].
clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
rewrite Esp. unfold qput_frame in FR5 |- *. apply (rw_cells_transport bsegs _ m6 m7 _ _ (rw_cells_transport bsegs _ m5 m6 _ _ FR5 MU6 WM6
ltac:(apply HWR; cbn [cells_size csize Nat.add]; clear - Hsp; lia)) MU7 WM7).
unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End MissG.
End RL_freeX.
Export RL_freeX.

Module RL_freeY.
Import X12c X0j9 X14x X0r0 X0ra X0j1 X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X18s X18k X18o X18l X18m X18n X16z X18d X18z X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141 X143 X140 X144 X145 X146 X147 X148 X149 X14a X14b X14i X14j X15y X15x X15z X163 X15s X12s X15p X16o.
Import RL_stmt RL_A2 RL_G RL_FH RL_freeV RL_freeW RL_freeX.

Definition enq_entry_st (usp T M n : Z) (gp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 M) (Z_to_bv 64 n) a5 a6 a7 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 qenq_entry) fc None m (seg_rom bsegs).

Definition mfg_post (Σ1 : rtsA) (M n : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (jf : list byte),
ms = refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (bv_unsigned sp + -2208 + -64)) gp t0' t1' t2'
(Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) a4' a5' a6' a7'
(Z_to_bv 64 M) (Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (bv_unsigned sp + -2056))
(Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc (l_T (lay Σ1)) 24 m5
/\ ARTc Σ1 m5 /\ mem_inv bsegs m5 /\ wmono bsegs m m5 /\ stk bsegs m5 lo (bv_unsigned sp + -2208 + -64)
/\ rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m5
/\ icpt_frame m5 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
/\ qput_frame m5 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46800)
s0 (Z_to_bv 64 (M + 16)) s2 s3
s4 s5 s6
/\ rw_cells bsegs m5 (bv_unsigned sp + -2208 + -64)
[CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (l_T (lay Σ1) + 208));
C8 (Z_to_bv 64 (bv_unsigned sp + -2056)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (l_T (lay Σ1) + 80)); C8 (Z_to_bv 64 QUAR);
C8 (Z_to_bv 64 0x4a234)].

Lemma miss_front_g : forall (Σ1 : rtsA) (M n : Z) (m : mem) (j0 : nat)
(ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (F : bvmap 5 word) (fc : bv 32)
(m4 : mem) (lo : Z),
rt_wf0 Σ1 -> 1 <= n <= 2 ^ 27 -> l_ACEIL (lay Σ1) <= lo -> lo + 0x10000 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
ARTc Σ1 m4 -> mem_inv bsegs m4 -> wmono bsegs m m4 -> stk bsegs m4 lo (bv_unsigned sp + -2208) ->
rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m4 -> icpt_frame m4 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5 ->
qput_frame m4 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46800)
s0 (Z_to_bv 64 (M + 16)) s2 s3
s4 s5 s6 ->
ca Σ1 24 = [] ->
(ql Σ1 = [] \/ exists pre ents0, nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch /\ ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents0)]
/\ length ents0 = 1021%nat) ->
evt bsegs (mfg_post Σ1 M n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(enq_entry_st (bv_unsigned sp) (l_T (lay Σ1)) M n gp t0' t1' t2' a5' a6' a7' s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4).
Proof.
intros Σ1 M n m j0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
HW1 Hn1 HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 HCA0 Hvar0.
set (usp := bv_unsigned sp) in *.
pose proof (geo_of_wf0 Σ1 HW1) as HG1.
pose proof (g_grant Σ1 HG1 (l_T (lay Σ1)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
pose proof (se_disj Σ1 HG1) as (T5 & T4 & ATP). pose proof (fk_prb Σ1 HG1) as (FP1 & FP2 & FP3 & FP4 & FP5).
pose proof (fk_aceil Σ1 HG1) as (AC1 & AC2).
assert (Hsp : l_ACEIL (lay Σ1) + 0x10000 <= usp) by (clear - HLO HLO2; lia).
assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp AC1; unfold USTACK_TOP, SHB in *; lia).
pose proof ART4 as (CR4 & PR4 & CA4 & CH4 & SR4 & QR4 & DR4 & FS4 & IR4 & SH4 & VIS4).
pose proof (CA4 24 ltac:(lia)) as (PC24 & _). rewrite HCA0 in PC24. cbn [length Z.of_nat] in PC24.
pose proof QR4 as (QT4 & _).
eapply evt_cut.
{ unfold enq_entry_st. destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
- rewrite HQL in QT4.
apply (qenq_miss_A_empty_spec (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ1) + 80)) y3 y4 y5 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (l_T (lay Σ1) + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4
(l_T (lay Σ1)) (usp + -2056) M n lo _ _ QT4 PC24);
rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
+ clear - GT1. lia.
+ clear - T5. unfold SEGTOP_A in *. lia.
+ clear - GT3 HLO. lia.
+ exact ST4.
+ clear - HLO2. lia.
+ clear - Hsp Husp. unfold USTACK_TOP in *. lia.
+ exact MI4.
- rewrite HQL in QT4. pose proof (qwf_ql _ HW1) as QWF. rewrite HQL in QWF.
pose proof HW1 as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq, HQL in Q1.
eapply (qenq_miss_A_full_spec (Z_to_bv 64 0x4a234) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ1) + 80)) y3 y4 y5 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (l_T (lay Σ1) + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4
(l_T (lay Σ1)) (usp + -2056) M n lo _ _ (l_SB (lay Σ1)) pre
(p_abeg (l_SB (lay Σ1)) 24 j0) ents0 HL0 QT4 QWF);
rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
+ eapply Z.le_lt_trans; [exact Q1 | reflexivity].
+ exact PC24.
+ clear - GT1. lia.
+ clear - T5. unfold SEGTOP_A in *. lia.
+ clear - GT3 HLO. lia.
+ clear - FP2 FP4 FP5 HLO. unfold r24. lia.
+ clear - FP4 FP5 ATP. unfold r24 in *. lia.
+ clear - FP1 FP4. lia.
+ exact ST4.
+ clear - HLO2. lia.
+ clear - Hsp Husp. unfold USTACK_TOP in *. lia.
+ exact MI4. }
intros ms P. destruct P as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & m5 & -> & MU5 & WM5 & MI5 & (jf & EF5) & ST5).
rewrite (unsigned_lit (usp + -2208)) in MU5, EF5, ST5 |- * by exact RSP.
apply evt_done.
pose proof HW1 as (_ & _ & _ & _ & (_ & _ & HBt & _) & _). pose proof HW1 as (_ & _ & _ & _ & _ & _ & _ & Dok1 & _).
assert (Ha : l_ACEIL (lay Σ1) <= usp + -2208 - 64) by (clear - Hsp; lia).
exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, m5, jf.
split; [reflexivity|].
split; [exact (ARTc_stack _ (usp + -2208 - 64) (usp + -2208) HG1 Ha m4 m5 ART4 MU5 WM5 HBt Dok1)|].
split; [exact MI5|]. split; [exact (wmono_trans bsegs _ _ _ WM4 WM5)|].
split; [replace (usp + -2208 + -64) with (usp + -2208 - 64) by ring; exact ST5|].
split.
{ intros a Ha'. rewrite (MU5 a); [exact (RP4 a Ha')|].
refine (kv_client Σ1 [(usp + -2208 - 64, usp + -2208)] [] [] [] usp HG1
(sk_img _ _ _ HG1 Ha) (sk_grant _ _ _ HG1 Ha) (sk_slot _ _ _ HG1 Ha) (sk_shad_app _ _ _ HG1 Ha) (sk_secmap _ _ _ HG1 Ha) _
ltac:(apply Forall_forall; intros; exact I) (live Σ1) _ _ Ha').
- intros a' k' H1 H2. cbn [disjoint_from]. split; [clear - H1; lia | exact I].
- intros p' n' Hin. pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
split.
{ apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). cbn [disjoint_from]. split; [clear; lia | exact I]. }
split.
{ unfold qput_frame in FR4 |- *. apply (rw_cells_transport bsegs _ m4 m5 _ _ FR4 MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
split; [clear; lia | exact I]. }
replace (usp + -2208 + -64) with (usp + -2208 - 64) by ring. exact EF5.
Qed.

Lemma rt_eager_en : forall Σ cal jB M n, rt_eager (enq_new Σ cal jB M n) = rt_eager Σ.
Proof.
intros Σ cal jB M n. apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
cbn [enq_new set_ql pop24 pr]. destruct (Z.eqb_spec k' 24) as [->|_]; [|split; reflexivity]. unfold upd_reg. cbn [r_muser r_mfa]. split; reflexivity.
Qed.

Section Stage.
Variables (Σ Σ1 : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
(F : bvmap 5 word) (fc : bv 32) (m m4 : mem) (lo M n p : Z) (T : TSet).
Hypothesis DRAIN : drain_stmt.
Hypothesis FC : fixed_commit_node.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis HW1 : rt_wf0 Σ1.
Hypothesis HP : pend_e Σ1 M n.
Hypothesis EL : live Σ1 = live_remove p (live Σ).
Hypothesis EF : frames Σ1 = frames Σ.
Hypothesis ELY : lay Σ1 = lay Σ.
Hypothesis EC : credit Σ1 = credit Σ.
Hypothesis EPO : rtA_pois Σ1 = rtA_pois Σ.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x10000 <= bv_unsigned sp.
Hypothesis Husp : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis ART4 : ARTc Σ1 m4.
Hypothesis MI4 : mem_inv bsegs m4.
Hypothesis WM4 : wmono bsegs m m4.
Hypothesis ST4 : stk bsegs m4 lo (bv_unsigned sp + -2208).
Hypothesis RP4 : rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m4.
Hypothesis ICF : icpt_frame m4 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5.
Hypothesis FR4 : qput_frame m4 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46800)
s0 (Z_to_bv 64 (M + 16)) s2 s3
s4 s5 s6.
Hypothesis Hk : forall c', rl_postF Σ PMc F fc ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m c' -> realizes bsegs c' T.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation entry := (enq_entry_st (bv_unsigned sp) (l_T (lay Σ1)) M n gp t0' t1' t2' a5' a6' a7' s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4).

Lemma es_n : 1 <= n <= 2 ^ 27.
Proof using HW1 HP. exact (pe_n Σ1 M n HW1 (proj1 HP)). Qed.

Lemma es_sp : l_ACEIL (lay Σ1) + 0x10000 <= usp.
Proof using ELY HLO HLO2. rewrite ELY. clear - HLO HLO2. lia. Qed.

Lemma es_fin : forall Σ2 c2, live Σ2 = live Σ1 -> frames Σ2 = frames Σ1 -> lay Σ2 = lay Σ1 -> credit Σ2 = credit Σ1 -> rtA_pois Σ2 = rtA_pois Σ1 ->
AST SEGTOP_A (rtA_allow Σ2) (enq_post Σ2 (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(fun mo => ARTM_A Σ2 mo /\ PMc mo) c2 -> realizes bsegs c2 T.
Proof using DRAIN FDO MST EL EF ELY EC EPO HLO HLO2 Husp Hk.
intros Σ2 c2 E1 E2 E3 E4 E5 Hc2.
apply (fin_from_enq DRAIN Σ Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p T c2 FDO MST
ltac:(rewrite E1; exact EL) ltac:(rewrite E2; exact EF) ltac:(rewrite E3; exact ELY) ltac:(rewrite E4; exact EC) ltac:(rewrite E5; exact EPO)
HLO HLO2 Husp); [|exact Hk].
rewrite E1, <- EF. exact Hc2.
Qed.

Lemma es_new : forall (j0 : nat) cf,
(ql Σ1 = [] \/ exists pre ents0, nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch /\ ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents0)]
/\ length ents0 = 1021%nat) ->
AST SEGTOP_A (rtA_allow Σ1) (eq entry) (fun mo => ARTM_A Σ1 mo /\ PMc mo) cf -> realizes bsegs cf T.
Proof using DRAIN FC FDO MST HW1 HP EL EF ELY EC EPO HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk.
intros j0 cf Hvar0 Hc. pose proof es_n as Hn1. pose proof es_sp as Hsp. pose proof (geo_of_wf0 Σ1 HW1) as HG1.
pose proof (fk_aceil Σ1 HG1) as (AC1 & AC2).
assert (HLO1 : l_ACEIL (lay Σ1) <= lo) by (rewrite ELY; exact HLO).
pose proof HW1 as (_ & (_ & _ & R3 & _) & _). destruct (R3 24 ltac:(lia)) as (_ & _ & CAF).
destruct (ca Σ1 24) as [|x l] eqn:ECA.
-
assert (W1 : forall ms, eq entry ms -> evt bsegs (mfg_post Σ1 M n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
by (intros ms <-; exact (miss_front_g Σ1 M n m j0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
HW1 Hn1 HLO1 HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 ECA Hvar0)).
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
intros c1 Hc1.
apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1]. apply AST_exI in Hc1 as [y3 Hc1].
apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1]. apply AST_exI in Hc1 as [y7 Hc1].
apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [y10 Hc1].
apply AST_exI in Hc1 as [m5 Hc1]. apply AST_exI in Hc1 as [jf Hc1].
pose proof Hc1 as (_ & (_ & ART5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5 & EF5) & _ & _).
assert (RSP : 0 <= usp + -2208 + -64 < 2 ^ 64) by (clear - Hsp Husp AC1; unfold USTACK_TOP, SHB in *; lia).
pose proof (pend_room_e Σ1 M n HW1 HP ECA) as HROOM.

pose proof HW1 as (_ & (HR1 & _) & _).
pose proof (refill_ca_len (pr Σ1 24) 24 ltac:(clear; lia) (HR1 24 ltac:(clear; lia))) as LCA.
change (MaxCount 24 / 2) with 1 in LCA.
pose proof (refill_wf0 Σ1 24 ltac:(clear; lia) HW1 ECA HROOM) as HWb.
pose proof HWb as (_ & (_ & _ & HR3 & _) & _). destruct (HR3 24 ltac:(clear; lia)) as (_ & _ & CAFb).
cbn [refillΣ ca] in CAFb. rewrite Z.eqb_refl in CAFb.
destruct (refill_ca (pr Σ1 24) 24) as [|xb [|yb lb]] eqn:ECAb; [cbn in LCA; lia | | cbn in LCA; lia].
pose proof (proj1 (Forall_forall _ _) CAFb xb (in_eq xb [])) as (Hxb & _).
set (jB := Z.to_nat xb).
assert (HjB : refill_ca (pr Σ1 24) 24 = [Z.of_nat jB]) by (rewrite ECAb; unfold jB; rewrite Z2Nat.id by (clear - Hxb; lia); reflexivity).
assert (Hc1' : AST SEGTOP_A (rtA_allow Σ1)
(eq (refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp y0 y1 y2
(Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) y3 y4 y5 y6
(Z_to_bv 64 M) (Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y7 y8 y9 y10 F fc (l_T (lay Σ1)) 24 m5))
(fun mo => ARTM_A Σ1 mo /\ PMc mo) c1).
{ eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E | intros mo X; exact X]. }
apply (refill_core Σ1 PMc m5 24 lo (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp
(Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) (Z_to_bv 64 M)
(Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 F fc
y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 FDO MST HW1 ART5 ltac:(clear; lia) ECA HROOM MI5
ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; exact ST5) HLO1
ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; clear - HLO2; lia)
ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; clear - Husp; unfold USTACK_TOP in *; lia) FC T c1 Hc1').
intros c2 Hc2.
assert (VAR : exists (jX : nat) (stX : ckst), nth_error (r_st (pr (refillΣ Σ1 24) 24)) jX = Some stX
/\ ((jX = jB /\ stX = CkIdle /\ ql Σ1 = [])
\/ (stX = CkBatch /\ exists pre ents0, ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 jX, ents0)] /\ length ents0 = 1021%nat))).
{ destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
- exists jB, CkIdle. split; [|left; split; [reflexivity|]; split; [reflexivity | exact HQL]].
exact (ng_jB _ [] jB HWb ltac:(cbn [refillΣ ca]; rewrite Z.eqb_refl; exact HjB)).
- exists j0, CkBatch. split; [|right; split; [reflexivity|]; exists pre, ents0; split; [exact HQL | exact HL0]].
exact (rfs_keep Σ1 24 ltac:(clear; lia) HW1 24 j0 _ Hj0). }
destruct VAR as (jX & stX & HjX & HvarX).
assert (W2 : forall ms, rf_post F fc Σ1 24 lo (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp
(Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) (Z_to_bv 64 M)
(Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 m5 ms ->
evt bsegs (fun ms' =>
enq_post (enq_new (refillΣ Σ1 24) [] jB M n) (live Σ1) (frames Σ1)
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms') ms).
{ intros ms (m6 & RET & ART6 & MI6 & WM6 & ST6 & MU6).
destruct RET as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & ->).
rewrite (ret_pc_even qenq_refill_ret) by (unfold qenq_refill_ret; first [reflexivity | lia]).
rewrite (unsigned_lit (usp + -2208 + -64)) in ST6, MU6 by exact RSP.
eapply evt_mono; [apply (miss_enq_g Σ1 M n m jB jX stX usp HW1 HP ECA Hsp HjB HjX HvarX
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m5 m6 lo jf (Z_to_bv 64 qenq_refill_ret)
z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 eq_refl HLO1 HLO2 Husp WM5 RP5 ICF5 FR5 EF5 ART6 MI6 WM6 ST6 MU6)|].
intros ms' P. exact P. }
apply (cps_realizes bsegs _ _ _ c2 (ast_evt bsegs SEGTOP_A asegs_wx asegs_below _ _ _ _ (fl_ASTA_mat_stable _ PMc MST) W2) Hc2).
intros c3 Hc3.
apply (es_fin (enq_new (refillΣ Σ1 24) [] jB M n) c3 eq_refl eq_refl eq_refl eq_refl eq_refl).
eapply AST_conseq; [exact Hc3 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
apply (artm_eq (refillΣ Σ1 24)); [reflexivity | reflexivity | exact (rt_eager_en _ [] jB M n) | exact HM].
-
destruct (exists_last (l := x :: l) ltac:(discriminate)) as (cal & xj & Ecal).
pose proof (proj1 (Forall_forall _ _) CAF xj ltac:(rewrite Ecal; apply in_or_app; right; left; reflexivity)) as (Hxj & _).
set (jB := Z.to_nat xj).
assert (HCA : ca Σ1 24 = cal ++ [Z.of_nat jB]) by (rewrite ECA, Ecal; unfold jB; rewrite Z2Nat.id by (clear - Hxj; lia); reflexivity).
assert (VAR : exists (jX : nat) (stX : ckst), nth_error (r_st (pr Σ1 24)) jX = Some stX
/\ ((jX = jB /\ stX = CkIdle /\ ql Σ1 = [])
\/ (stX = CkBatch /\ exists pre ents0, ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 jX, ents0)] /\ length ents0 = 1021%nat))).
{ destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
- exists jB, CkIdle. split; [exact (ng_jB Σ1 cal jB HW1 HCA)|]. left. split; [reflexivity|]. split; [reflexivity | exact HQL].
- exists j0, CkBatch. split; [exact Hj0|]. right. split; [reflexivity|]. exists pre, ents0. split; [exact HQL | exact HL0]. }
destruct VAR as (jX & stX & HjX & HvarX).
assert (W1 : forall ms, eq entry ms ->
evt bsegs (enq_post (enq_new Σ1 cal jB M n) (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
by (intros ms <-; exact (new_enq_g Σ1 M n m cal jB jX stX usp HW1 HP HCA HjX HvarX Hsp
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
eq_refl ART4 MI4 WM4 ST4 HLO1 HLO2 Husp RP4 ICF FR4)).
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
intros c1 Hc1. apply (es_fin (enq_new Σ1 cal jB M n) c1 eq_refl eq_refl eq_refl eq_refl eq_refl).
eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
apply (artm_eq Σ1); [reflexivity | reflexivity | exact (rt_eager_en Σ1 cal jB M n) | exact HM].
Qed.

Theorem enq_stage : forall cf, AST SEGTOP_A (rtA_allow Σ1) (eq entry) (fun mo => ARTM_A Σ1 mo /\ PMc mo) cf -> realizes bsegs cf T.
Proof using DRAIN FC FDO MST HW1 HP EL EF ELY EC EPO HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk.
intros cf Hc. pose proof es_n as Hn1. pose proof es_sp as Hsp.
pose proof HW1 as (_ & _ & _ & _ & (_ & _ & QB & _ & Q5 & _) & _).
destruct (ql Σ1) as [|b l] eqn:EQL; [exact (es_new 0 cf (or_introl EQL) Hc)|].
destruct (exists_last (l := b :: l) ltac:(discriminate)) as (pre & (b0 & ents) & Eql).
destruct (proj1 (Forall_forall _ _) QB (b0, ents) ltac:(rewrite Eql; apply in_or_app; left; apply in_or_app; right; left; reflexivity))
as (j0 & Hj0 & Eb0). cbn [fst] in Eb0.
assert (HQL : ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents)]) by (rewrite EQL, Eql, Eb0; reflexivity).
pose proof (proj1 (Forall_forall _ _) Q5 (b0, ents) ltac:(rewrite Eql; apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as HL5.
cbn [snd] in HL5.
destruct (Nat.lt_ge_cases (length ents) 1021) as [HL|HL].
-
assert (W1 : forall ms, eq entry ms ->
evt bsegs (enq_post (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])) (live Σ1) (frames Σ1)
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
by (intros ms <-; exact (app_enq_g Σ1 M n m pre j0 ents usp HW1 HP HQL Hj0 HL Hsp
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
eq_refl ART4 MI4 WM4 ST4 ltac:(rewrite ELY; exact HLO) HLO2 Husp RP4 ICF FR4)).
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
intros c1 Hc1. apply (es_fin (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])) c1 eq_refl eq_refl eq_refl eq_refl eq_refl).
eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
apply (artm_eq Σ1); [reflexivity | reflexivity | reflexivity | exact HM].
-
apply (es_new j0 cf); [|exact Hc]. right. exists pre, ents. split; [exact Hj0|]. split; [exact HQL | clear - HL HL5; lia].
Qed.

End Stage.
End RL_freeY.
Export RL_freeY.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Module RL_A2.
Import X0bp X0j9 X0ec X001 X00b X04b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0j6 X0gd X0go X0i7 X0ge X0hs X0gu X0fy X0fg X0da X0g4 X0d8 X0fq X0d7 X0eo X0f0 X0e4 X0d9 X0e5 X0db X0j5 X0ft.
Import RL_stmt .

Definition icpt_frame (m : mem) (usp : Z) (ra s0 s1 s2 s3 s4 s5 : word) : Prop :=
(exists s4r s3r s2r s1r s0r, rw_cells asegs m (usp + -2128) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x46604)])
/\ (exists jr, rw_cells asegs m (usp + -2080) [CB 8 jr; C8 (Z_to_bv 64 0x68684)])
/\ (exists jq, rw_cells asegs m (usp + -2064) [CB 8 jq])
/\ (exists w, rw_cells asegs m (usp + -2056) [C8 (Z_to_bv 64 (usp + -2040)); C8 w])
/\ (exists ws, u64arr asegs m (usp + -2040) ws /\ length ws = 255%nat).

Lemma icpt_frame_transport : forall W (m m' : mem) usp ra s0 s1 s2 s3 s4 s5, icpt_frame m usp ra s0 s1 s2 s3 s4 s5 ->
munch W m m' -> wmono asegs m m' -> disjoint_from W (usp - 2128) 2128 -> icpt_frame m' usp ra s0 s1 s2 s3 s4 s5.
Proof.
intros W m m' usp ra s0 s1 s2 s3 s4 s5 ((s4r & s3r & s2r & s1r & s0r & F1) & (jr & F2) & (jq & F3) & (w & F4) & (ws & F5 & F5l)) MU WM HD.
split; [|split; [|split; [|split]]].
- exists s4r, s3r, s2r, s1r, s0r. apply (rw_cells_transport asegs W m m' _ _ F1 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
- exists jr. apply (rw_cells_transport asegs W m m' _ _ F2 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
- exists jq. apply (rw_cells_transport asegs W m m' _ _ F3 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
- exists w. apply (rw_cells_transport asegs W m m' _ _ F4 MU WM). cbn [cells_size csize Nat.add]. apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | lia].
- exists ws. split; [|exact F5l]. apply (u64arr_transport asegs W m m' _ _ F5 MU WM). rewrite F5l.
apply (dsj_sub W (usp - 2128) 2128); [exact HD | lia | cbn; lia].
Qed.

Lemma icpt_frame_agree : forall (m m' : mem) usp ra s0 s1 s2 s3 s4 s5, icpt_frame m usp ra s0 s1 s2 s3 s4 s5 ->
(forall a : word, usp - 2128 <= bv_unsigned a < usp -> m' a = m a) -> icpt_frame m' usp ra s0 s1 s2 s3 s4 s5.
Proof.
intros m m' usp ra s0 s1 s2 s3 s4 s5 ((s4r & s3r & s2r & s1r & s0r & F1) & (jr & F2) & (jq & F3) & (w & F4) & (ws & F5 & F5l)) AG.
split; [|split; [|split; [|split]]].
- exists s4r, s3r, s2r, s1r, s0r. apply (X00b.rw_cells_agree_nw asegs m m' _ _ F1). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
- exists jr. apply (X00b.rw_cells_agree_nw asegs m m' _ _ F2). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
- exists jq. apply (X00b.rw_cells_agree_nw asegs m m' _ _ F3). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
- exists w. apply (X00b.rw_cells_agree_nw asegs m m' _ _ F4). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
- exists ws. split; [|exact F5l]. apply (X00b.u64arr_agree_nw asegs m m' _ _ F5). intros a Ha. apply AG. rewrite F5l in Ha. cbn in Ha. lia.
Qed.

Definition sA_run_post (Σ : rtsA) (c : Z) (i : nat) (n usp lo : Z) (tr : list Z) (gp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (l_T (lay Σ) + 208))
(Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 n) a5' a6' a7'
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (l_T (lay Σ) + 208))
(Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m' (seg_rom asegs)
/\ ARTc (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) m'
/\ mem_inv asegs m' /\ wmono asegs m m'
/\ munch (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp) m m'
/\ stk asegs m' lo (usp + -2208)
/\ qput_frame m' (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) s0
(Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16)) s2 s3 s4
s5 s6.

Lemma dp_hash1 : forall D tr, dep_inv D -> hash_of (d_hs (fst (depot_put D tr))) 1 = hash_of (d_hs D) 1.
Proof.
intros D tr (_ & _ & H1 & _). destruct (Z.eqb_spec (find_of (d_hs D) (depot_hash tr)) 0) as [E|E].
- rewrite (depot_put_miss D tr E). cbn [fst d_hs]. apply hash_of_snoc_old. unfold d_n in H1. lia.
- rewrite (depot_put_hit D tr E). reflexivity.
Qed.

Section SegRun.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n usp lo : Z) (tr : list Z) (tb : list word) (s0 s2 s3 s4 s5 : word).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis Hn1 : 1 <= n.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Husp : usp + 16 <= USTACK_TOP.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x10000 <= usp.
Hypothesis ST : stk asegs m lo (usp + -2128).
Hypothesis MI : mem_inv asegs m.
Hypothesis BC : rw_cells asegs m (usp + -2056) [C8 (Z_to_bv 64 (usp + -2040)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))].
Hypothesis TB : u64arr asegs m (usp + -2040) (wr_trace tr tb).
Hypothesis HTB : length tb = 255%nat.
Hypothesis Htr : In tr T_MAIN /\ (1 <= length tr <= 5)%nat.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation S := (ClassSize c).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation W := (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp).

Lemma sr_tcx : 0 < TCX /\ TCX + 0x10000 <= l_ACEIL L /\ (TCX + 0x10000 <= PRB \/ PRB + 0x2000011000 <= TCX)
/\ (TCX + 0x10000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= TCX) /\ (TCX + 0x10000 <= 0x10000 \/ SEGTOP_A <= TCX)
/\ (TCX + 0x10000 <= T \/ T + 4096 <= TCX).
Proof using HA.
clear - HA. pose proof (geo_grant Σ m HA TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & _ & X3 & X4 & X5).
pose proof (geo_apart Σ m HA 0 3 _ _ ltac:(lia) eq_refl eq_refl) as A03. pose proof (geo_apart Σ m HA 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23.
cbn [fst snd] in *. unfold apart in *. split; [exact X1|]. split; [exact X3|]. split; [lia|]. split; [exact X4|]. split; [exact X5|]. lia.
Qed.

Lemma sr_tr : In tr T_MAIN /\ (1 <= length tr <= 5)%nat /\ Forall rng64 tr.
Proof using Htr.
clear - Htr. destruct Htr as (H1 & H2). split; [exact H1|]. split; [exact H2|]. exact (T_MAIN_rng64 tr H1).
Qed.

Lemma fl_c8_of_stk : forall (m0 : mem) a, stk asegs m0 a (a + 8) -> exists w, rw_cells asegs m0 a [C8 w].
Proof.
clear. intros m0 a St. destruct (stk_bytes asegs m0 a (a + 8) St ltac:(lia)) as (bs & Hl & Hb). replace (a + 8 - a) with 8 in Hl by lia.
exists (le_bytes_to_word bs). split; [split|].
- cbn. tauto.
- cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite fl_le8_of_bytes by lia. exact Hb.
- cbn [cells_size csize Nat.add]. destruct St as (S0 & S1 & Sw). split; [lia|]. split; [lia|]. intros j Hj. exact (proj1 (Sw (a + j) ltac:(lia))).
Qed.

Lemma fl_two_c8 : forall (m0 : mem) a, stk asegs m0 a (a + 16) -> exists w1 w2, rw_cells asegs m0 a [C8 w1; C8 w2].
Proof.
clear. intros m0 a St. destruct (stk_split asegs m0 a (a + 8) (a + 16) St ltac:(lia)) as [S1 S2].
destruct (fl_c8_of_stk m0 a S1) as (w1 & H1). destruct (fl_c8_of_stk m0 (a + 8) ltac:(replace (a + 8 + 8) with (a + 16) by lia; exact S2)) as (w2 & H2).
exists w1, w2. change [C8 w1; C8 w2] with ([C8 w1] ++ [C8 w2]). apply rwc_app. split; [exact H1|]. exact H2.
Qed.

Lemma sr_geo2 : shad (M + 16) + ru8 n / 8 <= shad (AB + S) /\ SHB <= shad (M + 16) /\ 0 <= ru8 n / 8
/\ shad (rb SB c) <= shad (M + 16) /\ shad (M + 16) + ru8 n / 8 <= shad (rb SB c + 2 ^ 32).
Proof using HA Hc Hn Hn1.
clear - HA Hc Hn Hn1.
pose proof (sa_geo Σ m c i n HA Hc Hn Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
& K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
pose proof (fk_shad_mono (rb SB c) AB K7) as E1. pose proof (fk_shad_mono (AB + S) (rb SB c + 2 ^ 32)) as E2.
assert (AB + S <= rb SB c + 2 ^ 32) by (clear - K8 K10; unfold kUserCap in *; lia). specialize (E2 H).
split; [exact K16|]. split; [exact K30|]. split; [exact K40|]. split; [lia|]. lia.
Qed.

Lemma sr_M16 : M mod 16 = 0.
Proof using HA Hc.
clear - HA Hc. pose proof (geo_prb Σ m HA) as (_ & _ & P3). pose proof (ClassSize_range c Hc) as (_ & Hm). pose proof (rz_facts n) as (R1 & _).
unfold p_abeg. apply Z.mod_divide in P3, Hm, R1; try (clear; lia). destruct P3 as [q1 E1]. destruct Hm as [q2 E2]. destruct R1 as [q3 E3].
rewrite E1, E2, E3. replace (q1 * 2 ^ 16 + c * 2 ^ 32 + Z.of_nat i * (q2 * 32) + q3 * 16 - 16) with ((q1 * 4096 + c * 2 ^ 28 + Z.of_nat i * q2 * 2 + q3 - 1) * 16) by ring.
apply Z.mod_mul. lia.
Qed.

Lemma segA_run : forall gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32),
evt asegs (sA_run_post Σ c i n usp lo tr gp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
(MS (mkR (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0 (Z_to_bv 64 (M + 16))
(Z_to_bv 64 INST) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 1) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom asegs)).
Proof.
intros gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc.
pose proof (sa_geo Σ m c i n HA Hc Hn Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
& K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
pose proof (sa_disj Σ m HA) as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
pose proof sr_tcx as (X1 & X3 & XP & X4 & X5 & XT).
pose proof sr_tr as (TRM & TRL & TRR).
pose proof sr_geo2 as (G1 & G2 & G3 & G4 & G5).
pose proof sr_M16 as HM16.

destruct (ART_chunk Σ m HA) as [CP _]. destruct (CP c i (CkAlloc n) Hc Hn) as (WrA & (b1 & ctx & Hb1 & HD) & LCH & SHA1 & SHA2).
clear CP.

pose proof (ART_consts Σ m HA) as (IC & MMG & TC & M2S & PS & SC & CC & ICR).
destruct ICR as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18 & I19 & I20
& I21 & I22 & I23 & I24 & I25 & I26 & I27 & I28 & I29 & I30 & I31 & I32 & I33 & I34 & I35 & I36 & I37 & I38).
clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22 I24 I25 I26 I27 I28 I29 I30 I37 I38.

pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
pose proof (ART_dep Σ m HA) as DREP. unfold dep_rep in DREP.

destruct (fl_CB_of_wr m AB S (M + 16) 8 WrA ltac:(lia) ltac:(cbn; lia)) as (uw & UW).
destruct (fl_two_c8 m (T + 2824) ltac:(destruct (stk_split asegs m (T + 2768) (T + 2824) (T + 3168) I32 ltac:(lia)) as [_ X];
destruct (stk_split asegs m (T + 2824) (T + 2840) (T + 3168) X ltac:(lia)) as [X' _];
replace (T + 2824 + 16) with (T + 2840) by lia; exact X')) as (fr & fd & STS).
pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1.
assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; exact Rb1).
rewrite <- Eb in HD. clear Eb.
assert (RSP : 0 <= usp + -2128 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).

eapply evt_cut.
{ apply (dealloc_p1_spec (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp t0 t1 t2 s0 (Z_to_bv 64 (M + 16)) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
M n (bv_unsigned b1) (usp + -2056) TCX T lo ctx fr fd uw); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
all: try exact ST.
all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
all: try (clear - K33 K4 HLO; lia).
all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
all: try (clear - X3 HLO; lia). all: try (clear - K20 HLO; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - ATP K32 K33; lia). all: try (clear - XP K32 K33; lia).
all: try (clear - HLO2; lia). all: try (clear - Husp; unfold USTACK_TOP in *; lia). }
intros ms2 P2.
destruct P2 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & fr' & fd' & m2 & -> & MU2 & WM2 & MI2 & HD2 & UW2 & STS2 & ST2).
rewrite (unsigned_lit (usp + -2128)) in MU2, ST2 by exact RSP.
assert (MW2 : munch W m m2).
{ lazymatch type of MU2 with munch ?W2 _ _ => apply (munch_weaken W2 _ m m2); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU2] end. }
pose proof (sa_consts Σ m c i n usp HA Hc Hn Hn1 Hsp m2 MW2 WM2) as CR2.
destruct CR2 as (_ & _ & TC2 & _ & _ & _ & _ & ICR2).
destruct ICR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J31 & _ & J33 & _ & _ & _ & _ & _).
lazymatch type of MU2 with munch ?W2 _ _ =>
apply (rw_cells_transport asegs W2 m m2 _ _) in BC; [| exact MU2 | exact WM2 |];
[| cbn [disjoint_from cells_size csize Nat.add]; clear - K33 K4 K20 Hsp; repeat split; try exact I; lia];
apply (u64arr_transport asegs W2 m m2 _ _) in TB; [| exact MU2 | exact WM2 |];
[| rewrite wr_trace_length by (rewrite HTB; clear - TRL; lia); rewrite HTB; cbn [disjoint_from]; clear - K33 K4 K20 Hsp;
repeat split; try exact I; lia] end.
lazymatch type of MU2 with munch ?W2 _ _ => apply (dep_rep_transport W2 L (dep Σ) m m2) in DREP; [| exact DOK | exact MU2 | exact WM2 |] end.
2:{ split; [|split].
- unfold dsjl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd disjoint_from]; repeat split; try exact I;
first [ (left; clear - K2 K32; unfold SEGTOP_A in *; lia) | (clear - T5 K19; unfold SEGTOP_A in *; lia)
| (left; clear - Hsp K4 K2; unfold SEGTOP_A in *; lia) ].
- cbn [disjoint_from]. repeat split; try exact I; [clear - APD K32 K33; lia | clear - ATD; lia | clear - K23 Hsp; lia].
- cbn [disjoint_from]. repeat split; try exact I; [clear - APS K32 K33; lia | clear - ATS; lia | clear - K26 Hsp; lia]. }
rewrite wr_trace_split in TB. replace (usp + -2040) with (usp + -2056 + 16) in BC, TB by lia.
rewrite <- (length_map (Z_to_bv 64) tr) in BC.

eapply evt_cut.
{ apply (qchunk_spec (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp u0 u1 u2 s0 (Z_to_bv 64 (M + 16)) u3 u4 u5 u6
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u7 u8 u9 u10 F fc m2
M n (bv_unsigned b1) (usp + -2056) TCX T lo ctx (Z_to_bv 64 18446744069414584320) (dep Σ)
(DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB (map (Z_to_bv 64) tr) (skipn (length tr) tb));
try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
all: try exact ST2.
all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
all: try (clear - K33 K4 HLO; lia).
all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
all: try (clear - X3 HLO; lia). all: try (clear - K20 HLO; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - APD K32 K33; lia). all: try (clear - APS K32 K33; lia).
all: try (clear - HLO2; lia). all: try (clear - Husp; unfold USTACK_TOP in *; lia).
all: try (rewrite length_map; clear - TRL; lia).
all: try (rewrite <- wr_trace_split, wr_trace_length by (rewrite HTB; clear - TRL; lia); exact HTB).
all: try (exact (depot_ok_mono _ _ _ _ _ DOK HLO)).
all: try (rewrite length_map; clear - DT TRL; lia).
all: try (rewrite map_unsigned_lits by exact TRR; unfold DEP_BK; right; apply in_map_iff; exists tr; split; [reflexivity | exact TRM]). }
intros ms3 P3.
destruct P3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & m3 & -> & MU3 & WM3 & MI3 & W16 & REP3 & TB3 & ST3).
rewrite (unsigned_lit (usp + -2128)) in MU3, ST3 by exact RSP.
assert (MW3 : munch W m m3).
{ apply (munch_trans _ m m2 m3 MW2).
lazymatch type of MU3 with munch ?W3 _ _ => apply (munch_weaken W3 _ m2 m3); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU3] end. }
pose proof (wmono_trans asegs _ _ _ WM2 WM3) as WM23.
pose proof (sa_consts Σ m c i n usp HA Hc Hn Hn1 Hsp m3 MW3 WM23) as CR3.
destruct CR3 as (_ & _ & _ & _ & PS3 & _ & _ & ICR3).
destruct ICR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& _ & _ & K23' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K35' & K36' & _ & _).
apply (rwc_app asegs _ _ [C8 (Z_to_bv 64 268435456)]) in K35'. destruct K35' as [QM K35']. cbn [cells_size csize Nat.add] in K35'.
apply (rwc_app asegs _ _ [C8 (Z_to_bv 64 241591905)]) in K35'. destruct K35' as [_ QC]. cbn [cells_size csize Nat.add] in QC.
change (i_q_max + Z.of_nat 8 + Z.of_nat 8) with 1023808 in QC. change i_q_max with 1023792 in QM.

lazymatch type of MU3 with munch ?W3 _ _ =>
apply (rw_cells_transport asegs W3 m2 m3 _ _) in HD2; [| exact MU3 | exact WM3 |];
[| cbn [disjoint_from cells_size csize Nat.add];
repeat split; try exact I;
first [ (left; clear; lia) | (right; clear - K2 K32; unfold SEGTOP_A in *; lia) | (clear - APD K32 K33; lia) | (clear - APS K32 K33; lia)
| (left; clear - K33 K4 Hsp; lia) ] ] end.

apply bytes_at_app in SHA1. destruct SHA1 as [_ SHU]. rewrite farun_lenZ in SHU by lia. rewrite <- K15 in SHU.
assert (SHC : rw_cells asegs m (shad (M + 16)) [CB (length (ushadow n)) (ushadow n)]).
{ destruct (ART_prim Σ m HA c Hc) as (_ & _ & _ & _ & _ & _ & SST).
apply (fl_CB_of_bytes m _ _ _ _ SHU SST G4). rewrite fl_ushadow_len by lia. exact G5. }
replace (length (ushadow n)) with (Z.to_nat (ru8' n / 8)) in SHC by (unfold ru8'; pose proof (fl_ushadow_len n ltac:(lia)) as U; unfold ru8 in U; lia).
lazymatch type of MU2 with munch ?W2 _ _ =>
apply (rw_cells_transport asegs W2 m m2 _ _) in SHC; [| exact MU2 | exact WM2 |];
[| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (unfold ru8'; apply Z.div_pos; lia);
change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (left; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (clear - T4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (left; clear - K27 K31 Hsp; lia) ] ] end.
lazymatch type of MU3 with munch ?W3 _ _ =>
apply (rw_cells_transport asegs W3 m2 m3 _ _) in SHC; [| exact MU3 | exact WM3 |];
[| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (unfold ru8'; apply Z.div_pos; lia);
change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (left; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (right; clear - K30; unfold SHB in *; lia)
| (clear - D4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (clear - S4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (left; clear - K27 K31 Hsp; lia) ] ] end.

eapply evt_mono.
{ apply (qput_A_spec (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) v0 v1 v2 s0 (Z_to_bv 64 (M + 16)) v3 v4
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v5 v6 v7 v8 F fc m3
(T + 80) (T + 208) (usp + -2056) M n (bv_unsigned b1) lo ctx (ushadow n)); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
all: try exact ST3.
all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
all: try (change (ru8' n) with (ru8 n); clear - K12 K39 K4 K28; unfold kHighMemEnd; lia).
all: try (change (ru8' n) with (ru8 n); clear - K12 K39 K4 HLO; lia).
all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
all: try (clear - HLO2; lia).
all: try (clear - HA HLO; pose proof (rta_sp0_win Σ m HA); unfold l_ACEIL, rtA_sp0, STACK_WIN, kHighShadowEnd in *; lia). }
intros ms4 P4.
destruct P4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & m4 & -> & MU4 & WM4 & MI4 & SH4 & FR4 & ST4).
rewrite (unsigned_lit (usp + -2128)) in MU4, ST4, FR4 by exact RSP.
assert (MW4 : munch W m m4).
{ apply (munch_trans _ m m3 m4 MW3).
lazymatch type of MU4 with munch ?W4 _ _ => apply (munch_weaken W4 _ m3 m4); [unfold W_A1; clear - Hsp; change (ru8' n) with (ru8 n); solve_sub_fp | exact MU4] end. }
pose proof (wmono_trans asegs _ _ _ WM23 WM4) as WM24.

assert (HQ : qhdr3 m4 M n).
{ lazymatch type of MU4 with munch ?W4 _ _ =>
apply (rw_cells_transport asegs W4 m3 m4 _ _) in HD2; [| exact MU4 | exact WM4 |];
[| cbn [disjoint_from cells_size csize Nat.add]; change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (right; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (left; clear - K33 K4 Hsp; lia) ] ];
apply (rw_cells_transport asegs W4 m3 m4 _ _) in W16; [| exact MU4 | exact WM4 |];
[| cbn [disjoint_from cells_size csize Nat.add]; change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (right; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (left; clear - K33 K4 Hsp; lia) ] ] end.
exists (Z_to_bv 8 (bv_unsigned b1)), ctx, (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr))))).
split; [rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite (Z.mod_small (bv_unsigned b1) 256) by exact Rb1; exact Hb1|].
change [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx;
C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]
with ([C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ++
[C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]).
apply rwc_app. split; [exact HD2|]. cbn [cells_size csize Nat.add]. exact W16. }

rewrite map_unsigned_lits in REP3 by exact TRR.
lazymatch type of MU4 with munch ?W4 _ _ =>
apply (depot_rep_frame _ _ _ _ lo W4 m3 m4) in REP3; [| | exact MU4 | exact WM4 | | | | | |] end.
2:{ apply (qc_depot_ok_put_ok _ _ _ _ _ (depot_ok_mono _ _ _ _ _ DOK HLO) DN). clear - DT TRL; lia. }
all: try (cbn [disjoint_from]; change (ru8' n) with (ru8 n); repeat split; try exact I;
first [ (right; clear - K30; unfold SHB in *; lia) | (left; clear - K2 Hsp K4; unfold SEGTOP_A in *; lia)
| (clear - D4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (clear - S4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
| (left; clear - K23 Hsp; lia) | (left; clear - K26 Hsp; lia) ]).
pose proof (segA_ART Σ m c i n usp HA Hc Hn Hn1 Hsp m4 (fst (depot_put (dep Σ) tr)) MW4 WM24 HQ SH4 REP3
(qc_depot_ok_put_ok (dep Σ) tr DNB SSB (l_ACEIL L) DOK DN ltac:(clear - DT TRL; lia)) (dep_inv_put (dep Σ) tr DINV TRM ltac:(clear - TRL; lia))
(dp_hash1 _ _ DINV)) as ART4.
unfold sA_run_post. do 10 eexists. exists m4. split.
{ rewrite (unsigned_lit (usp + -2128)) by exact RSP. replace (usp + -2128 + -80) with (usp + -2208) by lia. reflexivity. }
split; [exact ART4|]. split; [exact MI4|]. split; [exact WM24|]. split; [exact MW4|].
split; [replace (usp + -2208) with (usp + -2128 - 80) by lia; exact ST4|].
replace (usp + -2208) with (usp + -2128 - 80) by lia. exact FR4.
Qed.

End SegRun.
End RL_A2.
Export RL_A2.

Module RL_G.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0id X0i7 X0hz X0ge X0hs X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc X0e6 X0dd X0de X0dg.
Import RL_stmt RL_A2.

Definition enq_post (Σ2 : rtsA) (live0 : list (Z * Z)) (frames0 : list (Z * nat)) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w1 : word) (m' : mem),
ms = enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m'
/\ ARTc Σ2 m' /\ rt_wfx Σ2 /\ rt_count Σ2 /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp + -2208)
/\ rt_pres live0 frames0 (bv_unsigned sp) m m'
/\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
/\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ2) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46714)
s0 w1 s2 s3 s4 s5 s6.
End RL_G.
Export RL_G.

Module RL_FH.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0id X0i7 X0hz X0ge X0hs X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc X0e6 X0dd X0de X0dg X0di X0df.
Import RL_stmt RL_A2 RL_G.
Import X00b.

Definition rl_ret_st (usp : Z) (gp s0 w1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) y0 y1 y2 s0 w1 y3 y4 y5 y6 y7 y8 y9 y10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y11 y12 y13 y14) F (Z_to_bv 64 0x46714) fc None m (seg_rom asegs).

Definition fin_post (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m5 : mem) : machine_state -> Prop :=
fun ms => exists (w1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m' : mem),
ms = rl_ret_st (bv_unsigned sp) gp s0 w1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F fc m'
/\ ART_A Σ2 m' /\ mem_inv asegs m' /\ wmono asegs m5 m' /\ stk asegs m' lo (bv_unsigned sp + -2128)
/\ munch [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)] m5 m'.

Lemma ret_tail : forall (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
t3 t4 t5 t6 w1 wc ws : word) (F : bvmap 5 word) (fc : bv 32) (m5 : mem) (lo : Z),
geo_ok Σ2 -> ARTc Σ2 m5 -> rt_wfx Σ2 -> rt_count Σ2 -> X0fy.qbytes (ql Σ2) <= 0x100000 ->
mem_inv asegs m5 -> stk asegs m5 lo (bv_unsigned sp + -2208) -> l_ACEIL (lay Σ2) <= lo -> lo + 0x10000 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP ->
qput_frame m5 (bv_unsigned sp + -2208) wc ws (Z_to_bv 64 0x46714) s0 w1 s2 s3 s4 s5 s6 ->
evt asegs (fin_post Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m5)
(enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5).
Proof.
intros Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w1 wc ws F fc m5 lo
HG ART5 HWX HC HBY MI5 ST5 HLO HLO2 Husp FR5.
set (usp := bv_unsigned sp) in *.
pose proof (fk_aceil Σ2 HG) as (X1 & X2).
assert (RSP2 : 0 <= usp + -2128 < 2 ^ 64) by (clear - HLO HLO2 Husp X1; unfold USTACK_TOP, SHB in *; lia).
pose proof ART5 as (_ & _ & _ & _ & _ & QR & _). destruct QR as (QT & _).
pose proof QT as QT'. apply (proj1 (qcache_rep_iff _ _ _)) in QT'. destruct QT' as (QH & _).
unfold enq_ret_st.
replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80))
by (rewrite (unsigned_lit (usp + -2128)) by exact RSP2; f_equal; lia).
replace (usp + -2208) with (usp + -2128 - 80) in ST5, FR5 by lia.
pose proof (qbytes_nonneg _ _ (qwf_ql_x Σ2 HWX)) as QB0.
eapply evt_mono.
{ apply (qput_B_ret_spec (Z_to_bv 64 0x46714) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11
t3 t4 t5 t6 ra0 s0 w1 s2 s3 s4 s5 s6 wc ws F fc m5 (l_T (lay Σ2) + 80) (X0id.qbytes (ql Σ2)) lo
(Z_to_bv 64 (Z.of_nat (length (ql Σ2)))) (Z_to_bv 64 (qfirst (ql Σ2))) (Z_to_bv 64 (qlast (ql Σ2))));
try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP2.
all: try exact ST5. all: try exact FR5. all: try (clear - HLO2; lia). all: try (clear - X1 HLO; unfold SHB in *; lia).
rewrite qbytes_eq. clear - QB0 HBY. rewrite qbytes_eq in QB0. lia. }
intros ms6 P6. destruct P6 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6).
rewrite (unsigned_lit (usp + -2128)) in MU6, ST6 by exact RSP2. rewrite (ret_pc_even 0x46714) by (first [reflexivity | lia]).
assert (MU6' : munch [(usp - 2208, usp - 2128)] m5 m6).
{ lazymatch type of MU6 with munch ?W6 _ _ => apply (munch_weaken W6 _ m5 m6); [clear - HLO2; solve_sub_fp | exact MU6] end. }
unfold fin_post, rl_ret_st. exists w1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m6. split; [reflexivity|].
split; [|split; [exact MI6 | split; [exact WM6 | split; [exact ST6 | exact MU6']]]].
apply c_ART; [exact (rt_wf_of_x Σ2 HWX HC ltac:(clear - HBY; unfold QMAX_L; lia))|].
apply (ARTc_stack Σ2 (usp - 2208) (usp - 2128) HG ltac:(clear - HLO HLO2; lia) m5 m6 ART5 MU6' WM6).
- destruct HWX as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
- destruct HWX as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK.
Qed.

Definition rl_postF (Σ : rtsA) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(p lo : Z) (m : mem) : config -> Prop :=
fun c' => exists (Σ' : rtsA),
ASTA RTA Σ' PMc (fun ms => exists (w1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m' : mem),
ms = rl_ret_st (bv_unsigned sp) gp s0 w1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F fc m'
/\ ART_A Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -2128)
/\ rt_pres (live_remove p (live Σ)) (frames Σ) (bv_unsigned sp) m m'
/\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5) c'
/\ live Σ' = live_remove p (live Σ) /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ /\ rtA_pois Σ' = rtA_pois Σ.

Section Fin.
Hypothesis DRAIN : drain_stmt.

Theorem fin_from_enq : forall (Σ Σ2 : rtsA) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (lo p : Z) T cf,
fdfs_only PMc -> mat_stable PMc ->
live Σ2 = live_remove p (live Σ) -> frames Σ2 = frames Σ -> lay Σ2 = lay Σ -> credit Σ2 = credit Σ -> rtA_pois Σ2 = rtA_pois Σ ->
l_ACEIL (lay Σ) <= lo -> lo + 0x10000 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
AST SEGTOP_A (rtA_allow Σ2) (enq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(fun mo => ARTM_A Σ2 mo /\ PMc mo) cf ->
(forall c', rl_postF Σ PMc F fc ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m c' -> realizes asegs c' T) ->
realizes asegs cf T.
Proof.
intros Σ Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p T cf FDO MST EL EF ELY EC EP HLO HLO2 Husp Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (Hsp : l_ACEIL (lay Σ2) + 0x10000 <= usp) by (rewrite ELY; clear - HLO HLO2; lia).
destruct (Z_le_gt_dec (X0fy.qbytes (ql Σ2)) 0x100000) as [HBY|HBY].
-
assert (W1 : forall ms, enq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms ->
evt asegs (fun ms' => exists (w1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m' : mem),
ms' = rl_ret_st usp gp s0 w1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F fc m'
/\ ART_A Σ2 m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2128)
/\ rt_pres (live Σ2) (frames Σ) usp m m' /\ icpt_frame m' usp ra s0 s1 s2 s3 s4 s5) ms).
{ intros ms P. destruct P as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
& w1 & m5 & -> & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5).
pose proof (geo_of_wfx Σ2 WX5) as HG2.
eapply evt_mono; [apply (ret_tail Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
t3 t4 t5 t6 w1 _ _ F fc m5 lo HG2 ART5 WX5 WC5 HBY MI5 ST5 ltac:(rewrite ELY; exact HLO)
HLO2 Husp FR5)|].
intros ms' P'. destruct P' as (w1' & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m' & -> & ART' & MI' & WM' & ST' & MU').
exists w1', z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m'. split; [reflexivity|].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|].
split.
{ intros a Ha. rewrite (MU' a); [exact (RP5 a Ha)|].
pose proof (ART_wf Σ2 m' ART') as HW2. pose proof HW2 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
pose proof (aclient_split Σ2 (live Σ2) usp (bv_unsigned a) HG2 Hsp
ltac:(intros p0 n0 Hin; destruct (V3 p0 n0 Hin) as [X|(s & Hs & Hq & Hsn & ->)]; [left; exact X|];
right; destruct (In_nth_error _ _ Hs) as (k & Hk'); exists k, s; split; [exact Hk' | split; [exact Hq | split; [exact Hsn | reflexivity]]])
ltac:(rewrite EF; exact Ha)) as HO.
cbn [outside] in HO |- *. clear - HO Hsp. split; [lia | exact I]. }
apply (icpt_frame_transport _ m5 m' usp ra s0 s1 s2 s3 s4 s5 ICF5 MU' WM'). cbn [disjoint_from]. split; [clear; lia | exact I]. }
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ2) _ _ _ (fl_ASTA_mat_stable Σ2 PMc MST) W1) Hc).
intros c1 Hc1. apply Hk.
exists Σ2. split; [|split; [exact EL | split; [exact EF | split; [exact ELY | exact (conj EC EP)]]]].
unfold ASTA. eapply AST_conseq; [exact Hc1| |intros mo H; exact H].
intros ms (w1 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & ART' & MI' & ST' & RP' & ICF').
exists w1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m'. split; [reflexivity|].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite <- EL; exact RP' | exact ICF'].
-
destruct Hc as (Hmc & HP & HPM & HZ).
destruct HP as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
& w1 & m5 & E5 & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5).
assert (Hc' : ASTA RTA Σ2 PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ2) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4a148) fc None m5 (seg_rom asegs))) cf).
{ split; [exact Hmc|]. split; [unfold enq_ret_st in E5; exact (eq_sym E5)|]. split; [exact HPM | exact HZ]. }
apply (DRAIN Σ2 PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5 lo usp
s0 w1 s2 s3 s4 s5 s6 FDO MST ART5 WX5 WC5 ltac:(clear - HBY; lia) FR5 ST5 ltac:(rewrite ELY; exact HLO) ltac:(clear - HLO2; lia)
ltac:(clear - Husp; unfold USTACK_TOP in *; lia) MI5 T cf Hc').
intros c2 (Σ' & Hc2 & EL' & EF' & ELY' & EC' & EP'). apply Hk.
exists Σ'. split; [|split; [exact (eq_trans EL' EL) | split; [exact (eq_trans EF' EF) | split; [exact (eq_trans ELY' ELY) | exact (conj (eq_trans EC' EC) (eq_trans EP' EP))]]]].
unfold ASTA in *. eapply AST_conseq; [exact Hc2| |intros mo H; exact H].
intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & ART6 & MI6 & ST6 & RP6).
exists w1, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m6. split; [reflexivity|].
split; [exact ART6|]. split; [exact MI6|]. split; [exact ST6|].
assert (AG : forall a : word, usp - 2128 <= bv_unsigned a < usp -> m6 a = m5 a).
{ intros a Ha. apply RP6. left. clear - Ha Husp. unfold USTACK_TOP in *. lia. }
split; [|exact (icpt_frame_agree m5 m6 usp ra s0 s1 s2 s3 s4 s5 ICF5 AG)].
intros a Ha. rewrite (RP6 a) by (rewrite EL, EF; destruct Ha as [Ha|Ha]; [left; unfold USTACK_TOP in *; lia | right; exact Ha]).
exact (RP5 a ltac:(rewrite EL; exact Ha)).
Qed.

End Fin.
End RL_FH.
Export RL_FH.

Module RL_freeV.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0id X0i7 X0hz X0ge X0hs X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc X0e6 X0dd X0de X0dg X0di X0dk X0dq X0dx X0dy.
Import RL_stmt RL_A2 RL_G RL_FH.

Section AppG.
Variables (Σ1 : rtsA) (M n : Z) (m : mem) (pre : list batch) (j0 : nat) (ents : list (Z * Z)) (usp : Z).
Hypothesis HW1 : rt_wf0 Σ1.
Hypothesis HP : pend_e Σ1 M n.
Hypothesis HQL : ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents)].
Hypothesis Hj0 : nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch.
Hypothesis HL : (length ents < 1021)%nat.
Hypothesis Hsp : l_ACEIL (lay Σ1) + 0x10000 <= usp.
#[local] Notation L := (lay Σ1).
#[local] Notation T := (l_T (lay Σ1)).
#[local] Notation SB := (l_SB (lay Σ1)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ1)) 24 j0).
#[local] Notation W := (W_E (l_T (lay Σ1)) (p_abeg (l_SB (lay Σ1)) 24 j0) (p_abeg (l_SB (lay Σ1)) 24 j0) usp).
#[local] Notation Wa := [(l_T (lay Σ1) + 80, l_T (lay Σ1) + 112); (p_abeg (l_SB (lay Σ1)) 24 j0, p_abeg (l_SB (lay Σ1)) 24 j0 + 8192); (usp - 2400, usp)].
#[local] Notation Σ2 := (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])).

Theorem app_ART_g : forall (m4 m' : mem) (ql' : list batch), ARTc Σ1 m4 -> munch Wa m4 m' -> wmono asegs m4 m' ->
qcache_rep m' (qcacheT T) ql' -> ARTc (set_ql Σ1 ql') m'.
Proof using HW1 HQL Hj0 HL Hsp.
intros m4 m' ql' ART4 MU WM QT. pose proof (geo_of_wf0 Σ1 HW1) as HG. pose proof HW1 as (_ & _ & _ & _ & _ & _ & _ & Dok & _).
assert (MW : munch W m4 m') by (apply (munch_weaken Wa _ m4 m'); [unfold W_E; clear; solve_sub_fp | exact MU]).
pose proof (se_img Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWi. pose proof (se_Tz Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWt.
pose proof (se_grant Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWg. pose proof (se_ris Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWr.
pose proof (se_fa Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWf. pose proof (se_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWs.
pose proof (se_shad_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWss. pose proof (se_shad_reg Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWsr.
pose proof (se_shad_app Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWsa. pose proof (se_secmap Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) as HWm.
destruct ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
pose proof (g_grant Σ1 HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
apply ARTc_intro; cbn [set_ql lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 ia_init credit live frames fsc] in *.
-
apply (consts_rep_frame L m4 m' CR); [|exact WM]. intros a Ha. apply MW.
destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
+ rewrite E. unfold W_E. cbn [outside]. pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (_ & _ & _ & K4 & K5 & K6 & K7 & K8 & _ & _ & K11 & K12 & _ & K14 & _).
pose proof (se_disj Σ1 HG) as (_ & _ & ATP). clear - K4 K5 K6 K7 K8 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
+ apply (kv_consts Σ1 W (TZ_E T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_E; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
-
intros c' Hc'. pose proof (PR c' Hc') as X. cbn [pr lay set_ql] in X |- *.
exact (reg_rep_transport W _ c' _ m4 m' X MW WM (kv_reg Σ1 W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0) (fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c' Hc' ltac:(intros []))).
-
intros c' Hc'. pose proof (CA c' Hc') as X. cbn [lay pr ca ca_init set_ql] in X |- *. destruct (Z.eq_dec c' 24) as [->|Hcc].
+ apply (pclass_rep_transport Wa _ 24 _ _ m4 m' X MU WM). unfold pclass_avoid, pc_addr, cacheT. cbn [disjoint_from].
pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (_ & _ & _ & K4 & K5 & K6 & K7 & K8 & _ & _ & K11 & K12 & _ & K14 & _).
pose proof (se_disj Σ1 HG) as (_ & _ & ATP). clear - K4 K5 K6 K7 K8 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
split; [lia|]. split; [lia|]. split; [lia | exact I].
+ apply (pclass_rep_transport W _ c' _ _ m4 m' X MW WM). apply (kv_pclass Σ1 W (TZ_E T) HWt c' Hc').
unfold TZ_E, pc_addr, cacheT. cbn [disjoint_from]. clear - Hc' Hcc. repeat split; try exact I; lia.
-
destruct CH as [P Sc]. split.
+ intros c' i' st Hc' Hn'. pose proof (P c' i' st Hc' Hn') as X. cbn [lay pr set_ql] in X, Hn' |- *. pose proof Hn' as Hn0.
{ assert (HD : (c' = 24 /\ i' = j0) \/ ~ In (c', i') [(24, j0); (24, j0)]).
{ destruct (Z.eq_dec c' 24) as [->|X1]; [destruct (Nat.eq_dec i' j0) as [->|X2]; [left; split; reflexivity|]|].
- right. intros Hin. apply X2. destruct Hin as [E|[E|[]]]; injection E; auto.
- right. intros Hin. apply X1. destruct Hin as [E|[E|[]]]; injection E; auto. }
destruct HD as [(-> & ->)|Hnin].
--
rewrite Hj0 in Hn0. injection Hn0 as <-. apply (pchunk_transport W _ 24 j0 _ m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp j0 CkBatch Hj0).
-- apply (pchunk_transport W _ c' i' _ m4 m' X MW WM). exact (kv_pchunk Σ1 W _ HG HWs HWss c' i' st Hc' Hn0 Hnin). }
+ intros k s Hk. apply (schunk_transport W k s m4 m' (Sc k s Hk) MW WM). exact (kv_schunk Σ1 W [] HG HWsa HWm k s Hk ltac:(intros [])).
-
exact (sec_rep_transport W _ m4 m' SR MW WM (kv_sec Σ1 W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
-
destruct QR as (_ & (QG & CG) & MX). split; [exact QT|]. split.
+ split; [apply (rw_cells_transport asegs W m4 m' _ _ QG MW WM); cbn [cells_size csize Nat.add]; apply HWi; [unfold i_q_global, INST, g_instance; lia | unfold i_q_global, INST, g_instance, SEGTOP_A; lia | exact I]|].
apply (qchain_transport W m4 m' _ CG MW WM). pose proof HW1 as (_ & _ & _ & _ & (_ & _ & QB & QN & _) & _).
apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) QB b ltac:(apply in_or_app; right; exact Hb)) as (j & Hj & Eb). rewrite Eb.
assert (Hjne : j <> j0).
{ intros ->. rewrite HQL in QN. rewrite <- app_assoc, map_app in QN. cbn [app map fst] in QN. apply NoDup_ListNoDup in QN.
apply (NoDup_remove_2 (map fst pre) (map fst (qg Σ1)) b0 QN). apply in_or_app. right. rewrite <- Eb. apply in_map. exact Hb. }
apply (HWs 24 j CkBatch); [lia | exact Hj | intros [E|[E|[]]]; injection E as E; exact (Hjne (eq_sym E)) | lia | change (ClassSize 24) with 8192; lia].
+ apply (rw_cells_transport asegs W m4 m' _ _ MX MW WM). cbn [cells_size csize Nat.add].
apply HWi; [unfold i_q_cmutex, INST, g_instance; lia | unfold i_q_cmutex, INST, g_instance, SEGTOP_A; lia | exact I].
-
exact (dep_rep_transport W L (dep Σ1) m4 m' DR Dok MW WM (kv_dep Σ1 W [] HWi ltac:(apply Forall_forall; intros; exact I)
(se_grant67 Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp))).
-
exact (fs_rep_transport W _ m4 m' FR MW WM (kv_fs Σ1 W [] (TZ_E T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
ltac:(unfold TZ_E; cbn; repeat split; try exact I; lia))).
- exact (ia_rep_transport W _ m4 m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
- exact (shadow_rep_transport W _ _ m4 m' SHR MW WM (kv_shadow Σ1 W [] HG HWsa)).
- exact (vis_rep_wmono _ m4 m' VIS WM).
Qed.

Lemma app_enq_g : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
(F : bvmap 5 word) (fc : bv 32) (m4 : mem) (lo : Z),
bv_unsigned sp = usp -> ARTc Σ1 m4 -> mem_inv asegs m4 -> wmono asegs m m4 ->
stk asegs m4 lo (usp + -2208) -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
rt_pres (live Σ1) (frames Σ1) usp m m4 ->
icpt_frame m4 usp ra s0 s1 s2 s3 s4 s5 ->
qput_frame m4 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) s0
(Z_to_bv 64 (M + 16)) s2 s3 s4 s5 s6 ->
evt asegs (enq_post Σ2 (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 M) (Z_to_bv 64 n) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m4 (seg_rom asegs)).
Proof using HW1 HP HQL Hj0 HL Hsp.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
Esp ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4.
pose proof (geo_of_wf0 Σ1 HW1) as HG.
pose proof (se_geo Σ1 j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (se_disj Σ1 HG) as (T5 & T4 & ATP).
assert (Hn1 : 1 <= n <= 2 ^ 27) by (pose proof HP as (QE & _); exact (pe_n Σ1 M n HW1 QE)).
assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
pose proof (qwf_ql Σ1 HW1) as QWF. rewrite HQL in QWF.
pose proof HW1 as (_ & _ & _ & _ & (Q1 & _) & _).
pose proof ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
pose proof QR as (QT & _). cbn [ql lay] in QT. rewrite HQL in QT.
rewrite HQL, <- qbytes_eq in Q1.
eapply evt_mono.
{ apply (qenq_app_spec (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4
(T + 80) (T + 208) (usp + -2056) M n SB lo pre b0 ents);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
all: try (clear - Hn1; lia).
all: try exact ST4.
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - K13; lia). all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
eapply Z.le_lt_trans; [apply Z.add_le_mono; [exact Q1 | exact (proj2 Hn1)] | reflexivity]. }
intros ms5 P5. destruct P5 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m5 & -> & MU5 & WM5 & MI5 & QR5 & _ & ST5).
rewrite (unsigned_lit (usp + -2208)) in MU5, ST5 by exact RSP. rewrite (ret_pc_even 0x4a148) by (first [reflexivity | lia]).
assert (MWa : munch [(T + 80, T + 112); (b0, b0 + 8192); (usp - 2400, usp)] m4 m5).
{ lazymatch type of MU5 with munch ?W5 _ _ => apply (munch_weaken W5 _ m4 m5); [clear - Hsp; solve_sub_fp | exact MU5] end. }
unfold enq_post. exists (Z_to_bv 64 0x4a148), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2056)),
(Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 (M + 16)), m5.
split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
split; [exact (app_ART_g m4 m5 _ ART4 MWa WM5 QR5)|].
destruct (app_wfx_e Σ1 M n pre j0 ents HW1 HP HQL HL) as (WX & WC).
split; [exact WX|]. split; [exact WC|]. split; [exact MI5|]. split; [exact (wmono_trans asegs _ _ _ WM4 WM5)|].
split; [rewrite Esp; exact ST5|].
split.
{ rewrite Esp. intros a Ha. rewrite (MWa a); [exact (RP4 a Ha)|].
assert (HO : outside (W_E (l_T (lay Σ1)) b0 b0 usp) (bv_unsigned a)).
{ apply (kv_client Σ1 _ [(24, j0); (24, j0)] [] [] usp HG
(se_img Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_grant Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
(se_slot Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_shad_app Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
(se_secmap Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_stack Σ1 j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
ltac:(apply Forall_forall; intros; exact I) (live Σ1)); [|exact Ha].
intros p' n' Hin.
pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
intros [E|[E|[]]]; injection E as <- <-; rewrite Hj0 in Hn'; discriminate.
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
revert HO. apply sub_fp_covered. unfold W_E. cbn [all_covered covered]. clear - Hsp.
split; [left; split; lia|]. split; [right; right; right; left; split; lia|]. split; [right; right; right; right; right; left; split; lia | exact I]. }
split.
{ rewrite Esp. apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). cbn [disjoint_from].
clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
rewrite Esp. unfold qput_frame in FR4 |- *. apply (rw_cells_transport asegs _ m4 m5 _ _ FR4 MU5 WM5).
cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End AppG.
End RL_freeV.
Export RL_freeV.

Module RL_freeW.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0id X0i7 X0hz X0i3 X0i0 X0ge X0hs X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc X0e6 X0dd X0de X0dg X0di X0dk X0dl X0dn X0dq X0dx X0dy.
Import RL_stmt RL_A2 RL_G RL_FH RL_freeV.

Section NewG2.
Variables (Σ : rtsA) (M n : Z) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σ)) 24 j0) (map fst (ql Σ))).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Theorem new_ART_g : forall (m4 m' : mem), ARTc Σ m4 -> munch W m4 m' -> wmono asegs m4 m' ->
qcache_rep m' (qcacheT T) (ql Σ ++ [(bB, [(M, n)])]) -> pclass_rep T 24 (ca_init Σ) cal m' -> ARTc (enq_new Σ cal jB M n) m'.
Proof using HW0 HCA Hj0 Hvar Hsp.
intros m4 m' ART4 MW WM QT PC24.
pose proof (ng_geo Σ HW0) as HG. pose proof (ng_jB Σ cal jB HW0 HCA) as HjB.
pose proof (se_img Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWi. pose proof (se_Tz Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWt.
pose proof (se_grant Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWg. pose proof (se_ris Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWr.
pose proof (se_fa Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWf. pose proof (se_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWs.
pose proof (se_shad_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWss. pose proof (se_shad_reg Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWsr.
pose proof (se_shad_app Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWsa. pose proof (se_secmap Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWm.
pose proof (se_geo Σ j0 jB st0 CkIdle HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
assert (RA : forall c', 1 <= c' <= 31 -> reg_avoid W SB c' (pr Σ c')).
{ intros c' Hc'. exact (kv_reg Σ W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0)
(fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c' Hc' ltac:(intros [])). }
destruct ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
apply ARTc_intro.
-
cbn [enq_new pop24 set_ql lay] in *.
apply (consts_rep_frame L m4 m' CR); [|exact WM]. intros a Ha. apply MW.
destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
+ rewrite E. unfold W_E. cbn [outside]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
+ apply (kv_consts Σ W (TZ_E T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_E; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
-
intros c' Hc'. pose proof (PR c' Hc') as X. cbn [enq_new pop24 set_ql lay pr] in X |- *.
destruct (Z.eqb_spec c' 24) as [->|Hcc].
+ exact (reg_rep_transport W _ 24 _ m4 m' (reg_rep_upd _ _ _ jB CkBatch m4 X) MW WM (reg_avoid_upd _ _ _ _ _ _ (RA 24 ltac:(lia)))).
+ exact (reg_rep_transport W _ c' _ m4 m' X MW WM (RA c' Hc')).
-
intros c' Hc'. pose proof (CA c' Hc') as X. cbn [enq_new pop24 set_ql lay pr ca ca_init] in X |- *.
destruct (Z.eqb_spec c' 24) as [->|Hcc]; [exact PC24|].
apply (pclass_rep_transport W _ c' _ _ m4 m' X MW WM). apply (kv_pclass Σ W (TZ_E T) HWt c' Hc').
unfold TZ_E, pc_addr, cacheT. cbn [disjoint_from]. clear - Hc' Hcc. repeat split; try exact I; lia.
-
destruct CH as [P Sc]. split.
+ intros c' i' st Hc' Hn'. cbn [enq_new set_ql lay] in Hn' |- *.
destruct (pop24_st Σ cal jB c' i' st Hn') as [(-> & -> & ->)|(Hne & Hn1)].
*
pose proof (P 24 jB CkIdle ltac:(lia) HjB) as X.
cbn [lay pchunk] in X |- *. destruct X as (_ & X).
apply (pchunk_transport W _ 24 jB CkBatch m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp jB CkIdle HjB).
* pose proof (P c' i' st Hc' Hn1) as X. cbn [lay] in X, Hn1 |- *.
assert (HD : (c' = 24 /\ i' = j0) \/ ~ In (c', i') [(24, j0); (24, jB)]).
{ destruct (Z.eq_dec c' 24) as [->|X1]; [destruct (Nat.eq_dec i' j0) as [->|X2]; [left; split; reflexivity|]|].
- right. intros Hin. destruct Hin as [E|[E|[]]]; injection E as E; [exact (X2 (eq_sym E))|].
destruct Hne as [Y|Y]; [exact (Y eq_refl) | exact (Y (eq_sym E))].
- right. intros Hin. apply X1. destruct Hin as [E|[E|[]]]; injection E; auto. }
destruct HD as [(-> & ->)|Hnin].
--
rewrite Hj0 in Hn1. injection Hn1 as Est. destruct Hvar as [(E & _)|(E0 & _)]; [destruct Hne as [Y|Y]; [exfalso; exact (Y eq_refl) | exfalso; exact (Y E)]|].
rewrite <- Est, E0 in X |- *.
apply (pchunk_transport W _ 24 j0 _ m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp j0 st0 Hj0).
-- apply (pchunk_transport W _ c' i' _ m4 m' X MW WM). exact (kv_pchunk Σ W _ HG HWs HWss c' i' st Hc' Hn1 Hnin).
+ intros k s Hk. cbn [enq_new pop24 set_ql sec] in Hk |- *.
apply (schunk_transport W k s m4 m' (Sc k s Hk) MW WM). exact (kv_schunk Σ W [] HG HWsa HWm k s Hk ltac:(intros [])).
-
cbn [enq_new pop24 set_ql] in *.
exact (sec_rep_transport W _ m4 m' SR MW WM (kv_sec Σ W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
-
cbn [enq_new pop24 set_ql ql qg lay] in *.
destruct QR as (_ & (QG & CG) & MX). split; [exact QT|]. split.
+ split; [apply (rw_cells_transport asegs W m4 m' _ _ QG MW WM); cbn [cells_size csize Nat.add]; apply HWi; [unfold i_q_global, INST, g_instance; lia | unfold i_q_global, INST, g_instance, SEGTOP_A; lia | exact I]|].
apply (qchain_transport W m4 m' _ CG MW WM). pose proof HW0 as (_ & _ & _ & _ & (_ & _ & QB & QN & _) & _).
apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) QB b ltac:(apply in_or_app; right; exact Hb)) as (j & Hj & Eb). rewrite Eb.
assert (HjjB : j <> jB) by (intros ->; rewrite HjB in Hj; discriminate Hj).
assert (Hjj0 : j <> j0).
{ intros ->. destruct Hvar as [(E & _)|(_ & Hin)]; [exact (HjjB E)|].
rewrite map_app in QN. apply NoDup_ListNoDup in QN. apply (fl_nodup_app_not_in _ _ _ QN Hin). rewrite <- Eb. apply in_map. exact Hb. }
apply (HWs 24 j CkBatch); [lia | exact Hj | | lia | change (ClassSize 24) with 8192; lia].
intros [E|[E|[]]]; injection E as E; [exact (Hjj0 (eq_sym E)) | exact (HjjB (eq_sym E))].
+ apply (rw_cells_transport asegs W m4 m' _ _ MX MW WM). cbn [cells_size csize Nat.add].
apply HWi; [unfold i_q_cmutex, INST, g_instance; lia | unfold i_q_cmutex, INST, g_instance, SEGTOP_A; lia | exact I].
-
cbn [enq_new pop24 set_ql lay dep] in *. pose proof HW0 as (_ & _ & _ & _ & _ & _ & _ & Dok & _).
exact (dep_rep_transport W L (dep Σ) m4 m' DR Dok MW WM (kv_dep Σ W [] HWi ltac:(apply Forall_forall; intros; exact I)
(se_grant67 Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp))).
-
cbn [enq_new pop24 set_ql] in *.
exact (fs_rep_transport W _ m4 m' FR MW WM (kv_fs Σ W [] (TZ_E T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
ltac:(unfold TZ_E; cbn; repeat split; try exact I; lia))).
- cbn [enq_new pop24 set_ql] in *. exact (ia_rep_transport W _ m4 m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
- cbn [enq_new pop24 set_ql lay] in *. exact (shadow_rep_transport W _ _ m4 m' SHR MW WM (kv_shadow Σ W [] HG HWsa)).
- exact (vis_rep_wmono _ m4 m' VIS WM).
Qed.

End NewG2.

Section NewE.
Variables (Σ : rtsA) (M n : Z) (m : mem) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis HP : pend_e Σ M n.
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
\/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation Σ1 := Σ.
#[local] Notation Σ2 := (enq_new Σ cal jB M n).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Lemma new_enq_g : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
(F : bvmap 5 word) (fc : bv 32) (m4 : mem) (lo : Z),
bv_unsigned sp = usp -> ARTc Σ1 m4 -> mem_inv asegs m4 -> wmono asegs m m4 ->
stk asegs m4 lo (usp + -2208) -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
rt_pres (live Σ) (frames Σ) usp m m4 ->
icpt_frame m4 usp ra s0 s1 s2 s3 s4 s5 ->
qput_frame m4 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) s0
(Z_to_bv 64 (M + 16)) s2 s3 s4 s5 s6 ->
evt asegs (enq_post Σ2 (live Σ) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 M) (Z_to_bv 64 n) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m4 (seg_rom asegs)).
Proof using HW0 HP HCA Hj0 Hvar Hsp.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
Esp ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4.
pose proof (geo_of_wf0 Σ HW0) as HG.
pose proof (ng_jB Σ cal jB HW0 HCA) as HjB.
pose proof (se_geo Σ j0 jB st0 CkIdle HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
pose proof (g_grant Σ HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
pose proof (g_prb Σ HG) as (P1 & P2 & P3).
assert (Hn1 : 1 <= n <= 2 ^ 27) by (pose proof HP as (QE & _); exact (pe_n Σ M n HW0 QE)).
assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
pose proof ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).

destruct (new_wfx_e Σ cal jB M n HW0 HP HCA) as (WX & WC).
pose proof (qwf_ql_x _ WX) as QWF. cbn [enq_new set_ql ql pop24 lay free_p] in QWF.
pose proof HW0 as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq in Q1.

assert (Hinit : ca_init Σ = true).
{ destruct (ca_init Σ) eqn:E; [reflexivity|]. pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & _ & R4 & _).
rewrite (R4 E 24) in HCA. destruct cal; discriminate HCA. }
assert (Hcnt : 1 <= Z.of_nat (length (cal ++ [Z.of_nat jB])) <= 16).
{ pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & R3 & _). destruct (R3 24 ltac:(lia)) as (C1 & _). rewrite HCA in C1.
pose proof (MaxCount_range 24 ltac:(lia)) as (MC & _). rewrite length_app in C1 |- *. cbn [length] in C1 |- *. clear - C1 MC. lia. }
pose proof (CA 24 ltac:(lia)) as PC. cbn [ca ca_init free_p lay] in PC. rewrite HCA, Hinit in PC. destruct PC as (PCC & chs & ARR & Hlen & Hpre).
change (ClassSize 24) with 8192 in PCC.
assert (Hw : nth_error chs (Z.to_nat (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1)) = Some (cpw 24 (Z.of_nat jB))).
{ pose proof (fl_hit_w (cpw 24) (cal ++ [Z.of_nat jB]) chs ltac:(destruct cal; discriminate) Hpre) as X. rewrite last_last in X.
replace (Z.to_nat (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1)) with (length (cal ++ [Z.of_nat jB]) - 1)%nat by (clear; rewrite length_app; cbn [length]; lia).
exact X. }
assert (HAB : chunk_addr SB 24 (cpw 24 (Z.of_nat jB)) = bB).
{ rewrite fl_hit_addr; [rewrite Nat2Z.id; reflexivity | lia | | reflexivity]. change (ClassSize 24) with 8192. clear - K9 K10. unfold p_abeg, rb, kUserCap in *.
change (ClassSize 24) with 8192 in *. lia. }
pose proof (MaxCount_range 24 ltac:(lia)) as (MC1 & _).

assert (NC : exists stj jb, qnew_cells m4 T SB (Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb).
{ destruct CR as (CI & _ & _ & _ & _ & _ & _ & ICR). pose proof ICR as STS. do 31 (apply proj2 in STS). apply proj1 in STS.
cbn [lay free_p] in STS. destruct (stk_split asegs m4 (T + 2768) (T + 2784) (T + 3168) STS ltac:(lia)) as [_ STS1].
destruct (stk_split asegs m4 (T + 2784) (T + 2784 + 8) (T + 3168) STS1 ltac:(lia)) as [STS2 _].
destruct (fl_c8_of_stk m4 (T + 2784) STS2) as (stj & HST).
destruct CH as (P & _). pose proof (P 24 jB CkIdle ltac:(lia) HjB) as PB.
cbn [pchunk lay free_p] in PB. destruct PB as (PB & _). change (ClassSize 24) with 8192 in PB.
destruct (fl_CB_of_stk m4 bB 8192 PB) as (jb & HJB).
exists stj, jb. unfold qnew_cells. split; [exact PCC|]. split; [exact ARR|]. split; [exact HST|].
split; [cbn [lay free_p] in CI; destruct CI as (CI & _); exact (proj1 (proj1 (rwc_app asegs m4 i_spacebeg [C8 (Z_to_bv 64 SB)] _) CI))|].
rewrite HAB. exact HJB. }
destruct NC as (stj & jb & NC).

eapply (evt_mono asegs (qenq_post (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 F fc
[(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
(b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] (qcacheT T) (ql Σ ++ [(bB, [(M, n)])]) lo m4
(fun m' => qnew_after m' T SB (Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs))).
{ destruct Hvar as [(E1 & E2 & HQL)|(E1 & pre & ents0 & HQL & HL0)].
- pose proof QR as (QT & _). cbn [ql lay free_p] in QT. rewrite HQL in QT.
eapply evt_mono.
{ apply (qenq_new_hit_empty_spec (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4 T (usp + -2056) M n SB lo
(Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
all: try (clear - Hn1; lia). all: try (clear - MC1; lia).
all: try (clear - P3; unfold p_abeg; apply Z.mod_divide in P3; [|lia]; destruct P3 as [q Hq]; rewrite Hq;
replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat jB * ClassSize 24) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat jB) * 8192)
by (change (ClassSize 24) with 8192; ring); apply Z.mod_mul; lia).
all: try (clear - K9 K10; unfold r24, rb, kUserCap in *; lia).
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try exact ST4.
all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL.
eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp.
- pose proof QR as (QT & _). cbn [ql lay free_p] in QT. rewrite HQL in QT. rewrite HQL in QWF, Q1.
rewrite <- app_assoc in QWF. cbn [app] in QWF.
eapply evt_mono.
{ apply (qenq_new_hit_full_spec (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4 T (usp + -2056) M n SB lo
(Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb pre b0 ents0);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
all: try (clear - Hn1; lia). all: try (clear - MC1; lia).
all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try exact ST4. all: try exact QWF.
all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL, <- app_assoc. cbn [app].
eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp. }
intros ms5 P5. destruct P5 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m5 & -> & MU5 & WM5 & MI5 & QR5 & NA5 & ST5).
rewrite (ret_pc_even 0x4a148) by (first [reflexivity | lia]).
destruct NA5 as (NA1 & NA2 & _).
assert (HSUB : sub_fp [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
(b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] W).
{ clear - Hsp. unfold W_E, qcacheT, pc_addr, cstat_alloc. solve_sub_fp. }
assert (PC5 : pclass_rep T 24 (ca_init Σ) cal m5).
{ rewrite Hinit. split.
- replace (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1) with (Z.of_nat (length cal)) in NA1 by (clear; rewrite length_app; cbn [length]; lia).
change (ClassSize 24) with 8192. exact NA1.
- exists chs. split; [exact NA2|]. split; [exact Hlen|]. exact (firstn_snoc_map (cpw 24) cal (Z.of_nat jB) chs Hpre). }
assert (Hvar' : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In b0 (map fst (ql Σ)))).
{ destruct Hvar as [(E1 & E2 & _)|(E1 & pre & ents0 & HQL & _)]; [left; split; assumption|]. right. split; [exact E1|].
rewrite HQL, map_app. apply in_or_app. right. left. reflexivity. }
unfold enq_post. exists (Z_to_bv 64 0x4a148), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2056)),
(Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 (M + 16)), m5.
split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
split; [exact (new_ART_g Σ M n cal jB j0 st0 usp HW0 HCA Hj0 Hvar' Hsp m4 m5 ART4 (munch_weaken _ _ _ _ HSUB MU5) WM5 QR5 PC5)|].
split; [exact WX|]. split; [exact WC|]. split; [exact MI5|]. split; [exact (wmono_trans asegs _ _ _ WM4 WM5)|].
split; [rewrite Esp; rewrite (unsigned_lit (usp + -2208)) in ST5 by exact RSP; exact ST5|].
split.
{ rewrite Esp. intros a Ha. rewrite (MU5 a); [exact (RP4 a Ha)|]. apply HSUB.
apply (kv_client Σ _ [(24, j0); (24, jB)] [] [] usp HG
(se_img Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_grant Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
(se_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_shad_app Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
(se_secmap Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_stack Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
ltac:(apply Forall_forall; intros; exact I) (live Σ)); [|exact Ha].
intros p' n' Hin.
pose proof HW0 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
intros [E|[E|[]]]; injection E as <- <-; [rewrite Hj0 in Hn'; injection Hn' as Est; destruct Hvar' as [(_ & X)|(X & _)]; rewrite X in Est; discriminate Est
| rewrite HjB in Hn'; discriminate Hn'].
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
split.
{ rewrite Esp. apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from].
clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
rewrite Esp. unfold qput_frame in FR4 |- *. apply (rw_cells_transport asegs _ m4 m5 _ _ FR4 MU5 WM5).
unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End NewE.
End RL_freeW.
Export RL_freeW.

Module RL_freeX.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0id X0i7 X0hz X0i3 X0i0 X0i1 X0i2 X0ge X0hs X0ie X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc X0e6 X0dd X0de X0dg X0di X0df X0dj X0dk X0dl X0dm X0dn X0do X0dq X0dx X0dy X0fd X0fc X0fe X0fi X0c7.
Import RL_stmt RL_A2 RL_G RL_FH RL_freeV RL_freeW.

Section MissG.
Variables (Σ1 : rtsA) (M n : Z) (m : mem) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW1 : rt_wf0 Σ1.
Hypothesis HP : pend_e Σ1 M n.
Hypothesis HCA0 : ca Σ1 24 = [].
Hypothesis Hsp : l_ACEIL (lay Σ1) + 0x10000 <= usp.
#[local] Notation L := (lay Σ1).
#[local] Notation T := (l_T (lay Σ1)).
#[local] Notation SB := (l_SB (lay Σ1)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ1)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ1)) 24 jB).
#[local] Notation Σb := (refillΣ Σ1 24).
#[local] Notation Σ2 := (enq_new (refillΣ Σ1 24) [] jB M n).
#[local] Notation W := (W_E (l_T (lay Σ1)) (p_abeg (l_SB (lay Σ1)) 24 j0) (p_abeg (l_SB (lay Σ1)) 24 jB) usp).
Hypothesis HjB : refill_ca (pr Σ1 24) 24 = [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σb 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle /\ ql Σ1 = [])
\/ (st0 = CkBatch /\ exists pre ents0, ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents0)] /\ length ents0 = 1021%nat).

Lemma mx_room : refill_room Σ1 24.
Proof using HW1 HP HCA0. exact (pend_room_e Σ1 M n HW1 HP HCA0). Qed.

Lemma mx_wfb : rt_wf0 Σb.
Proof using HW1 HP HCA0. exact (refill_wf0 Σ1 24 ltac:(clear; lia) HW1 HCA0 mx_room). Qed.

Lemma mx_pendb : pend_e Σb M n.
Proof using HW1 HP. exact (pend_refill_e Σ1 M n HW1 HP). Qed.

Lemma mx_cab : ca Σb 24 = [] ++ [Z.of_nat jB].
Proof using HjB. cbn [refillΣ ca]. rewrite Z.eqb_refl. exact HjB. Qed.

Lemma mx_var : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σb)) 24 j0) (map fst (ql Σb))).
Proof using Hvar.
destruct Hvar as [(E1 & E2 & _)|(E1 & pre & ents0 & HQL & _)]; [left; split; assumption|]. right. split; [exact E1|].
cbn [refillΣ ql lay]. rewrite HQL, map_app. apply in_or_app. right. left. reflexivity.
Qed.

Lemma mx_rt_eager : rt_eager Σ2 = rt_eager Σb.
Proof.
apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
cbn [enq_new set_ql pop24 pr]. destruct (Z.eqb_spec k' 24) as [->|_]; [|split; reflexivity]. unfold upd_reg. cbn [r_muser r_mfa]. split; reflexivity.
Qed.

Lemma miss_enq_g : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m5 m6 : mem) (lo : Z) (jf : list byte) (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
bv_unsigned sp = usp -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
wmono asegs m m5 -> rt_pres (live Σ1) (frames Σ1) usp m m5 ->
icpt_frame m5 usp ra s0 s1 s2 s3 s4 s5 ->
qput_frame m5 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 0x46714) s0
(Z_to_bv 64 (M + 16)) s2 s3 s4 s5 s6 ->
rw_cells asegs m5 (usp + -2208 + -64) [CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (T + 208)); C8 (Z_to_bv 64 (usp + -2056));
C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (T + 80)); C8 (Z_to_bv 64 QUAR); C8 (Z_to_bv 64 0x4a148)] ->
ARTc Σb m6 -> mem_inv asegs m6 -> wmono asegs m5 m6 -> stk asegs m6 lo (usp + -2208 + -64) ->
munch (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) m5 m6 ->
evt asegs (enq_post Σ2 (live Σ2) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra0 (Z_to_bv 64 (usp + -2208 + -64)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (pc_addr T 24)) (Z_to_bv 64 (cacheT T))
(Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 M) (Z_to_bv 64 (qcacheT T)) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 n)
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 qenq_refill_ret) fc None m6 (seg_rom asegs)).
Proof using HW1 HP HCA0 Hsp HjB Hj0 Hvar.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m5 m6 lo jf ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
Esp HLO HLO2 Husp WM5 RP5 ICF FR5 EF5 ART6 MI6 WM6 ST6 MU6.
pose proof mx_wfb as HWb. pose proof mx_pendb as HPb. pose proof mx_cab as HCA. pose proof mx_var as Hvar'.
pose proof (geo_of_wf0 Σb HWb) as HG. pose proof (geo_of_wf0 Σ1 HW1) as HG1.
pose proof (ng_jB Σb [] jB HWb HCA) as HjB'.
change (lay Σb) with (lay Σ1) in *.
pose proof (se_geo Σb j0 jB st0 CkIdle HG Hj0 HjB') as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
pose proof (se_disj Σb HG) as (T5 & T4 & ATP).
pose proof (g_prb Σb HG) as (P1 & P2 & P3).
change (lay Σb) with (lay Σ1) in *.
assert (Hn1 : 1 <= n <= 2 ^ 27) by (pose proof HP as (QE & _); exact (pe_n Σ1 M n HW1 QE)).
assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).

assert (HWR : forall a k, usp + -2208 + -64 <= a -> a + k <= usp -> disjoint_from (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) a k).
{ intros a k H1 H2. pose proof (rz_geo Σ1 24 HG1 ltac:(lia)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
pose proof (rz_shad Σ1 24 HG1 ltac:(lia)) as (S1 & S2). pose proof (se_disj Σ1 HG1) as (Z5 & Z4 & ZTP).
cbn [lay free_p] in *. unfold W_R. cbn [disjoint_from]. clear - H1 H2 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 Y12 S1 S2 Hsp K14 K15 K4 K6.
unfold rb, kUserCap, rinfo, RIS_of, SHB in *. repeat split; try exact I; lia. }
assert (EF6 : rw_cells asegs m6 (usp + -2208 + -64) [CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (T + 208)); C8 (Z_to_bv 64 (usp + -2056));
C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (T + 80)); C8 (Z_to_bv 64 QUAR); C8 (Z_to_bv 64 0x4a148)]).
{ apply (rw_cells_transport asegs _ m5 m6 _ _ EF5 MU6 WM6). apply HWR; cbn [cells_size csize Nat.add]; clear - Hsp; lia. }
pose proof (g_grant Σb HG (l_T (lay Σ1)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
pose proof ART6 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).

destruct (new_wfx_e Σb [] jB M n HWb HPb HCA) as (WX & WC).
pose proof (qwf_ql_x _ WX) as QWF. cbn [enq_new set_ql ql pop24 lay refillΣ free_p] in QWF.
pose proof HWb as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq in Q1. cbn [refillΣ ql free_p] in Q1.

assert (Hinit : ca_init Σb = true) by reflexivity.
pose proof (CA 24 ltac:(lia)) as PC. cbn [ca ca_init lay] in PC. rewrite Hinit in PC. rewrite HCA in PC.
destruct PC as (PCC & chs & ARR & Hlen & Hpre).
change (ClassSize 24) with 8192 in PCC.
assert (Hw : nth_error chs (Z.to_nat (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1)) = Some (cpw 24 (Z.of_nat jB))).
{ pose proof (fl_hit_w (cpw 24) ([] ++ [Z.of_nat jB]) chs ltac:(discriminate) Hpre) as X. rewrite last_last in X.
replace (Z.to_nat (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1)) with (length ([] ++ [Z.of_nat jB]) - 1)%nat by (clear; cbn [length app]; lia).
exact X. }
assert (HAB : chunk_addr SB 24 (cpw 24 (Z.of_nat jB)) = bB).
{ rewrite fl_hit_addr; [rewrite Nat2Z.id; reflexivity | lia | | reflexivity]. change (ClassSize 24) with 8192. clear - K9 K10. unfold p_abeg, rb, kUserCap in *.
change (ClassSize 24) with 8192 in *. lia. }
pose proof (MaxCount_range 24 ltac:(lia)) as (MC1 & _).

assert (NC : exists stj jb, qnew_cells m6 T SB (Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb).
{ destruct CR as (CI & _ & _ & _ & _ & _ & _ & ICR). pose proof ICR as STS. do 31 (apply proj2 in STS). apply proj1 in STS.
cbn [lay] in STS. destruct (stk_split asegs m6 (T + 2768) (T + 2784) (T + 3168) STS ltac:(lia)) as [_ STS1].
destruct (stk_split asegs m6 (T + 2784) (T + 2784 + 8) (T + 3168) STS1 ltac:(lia)) as [STS2 _].
destruct (fl_c8_of_stk m6 (T + 2784) STS2) as (stj & HST).
destruct CH as (P & _). pose proof (P 24 jB CkIdle ltac:(lia) HjB') as PB.
cbn [pchunk lay] in PB. destruct PB as (PB & _). change (ClassSize 24) with 8192 in PB.
destruct (fl_CB_of_stk m6 bB 8192 PB) as (jb & HJB).
exists stj, jb. unfold qnew_cells. split; [exact PCC|]. split; [exact ARR|]. split; [exact HST|].
split; [cbn [lay] in CI; destruct CI as (CI & _); exact (proj1 (proj1 (rwc_app asegs m6 i_spacebeg [C8 (Z_to_bv 64 SB)] _) CI))|].
rewrite HAB. exact HJB. }
destruct NC as (stj & jb & NC).

replace (usp + -2208 + -64) with (bv_unsigned (Z_to_bv 64 (usp + -2208)) + -64) by (rewrite (unsigned_lit (usp + -2208)) by exact RSP; reflexivity).
eapply (evt_mono asegs (qenq_post (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) (Z_to_bv 64 0x100000)
s7 s8 s9 s10 s11 F fc
[(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
(b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] (qcacheT T) (ql Σ1 ++ [(bB, [(M, n)])]) lo m6
(fun m' => qnew_after m' T SB (Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs))).
{ destruct Hvar as [(E1 & E2 & HQL)|(E1 & pre & ents0 & HQL & HL0)].
- pose proof QR as (QT & _). cbn [ql lay refillΣ free_p] in QT. rewrite HQL in QT.
eapply evt_mono.
{ apply (qenq_miss_B_empty_spec ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0x4a148) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) F fc m6 T (usp + -2056) M n SB lo
(Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb jf);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
all: try (clear - Hn1; lia). all: try (clear - MC1; lia). all: try (clear; cbn; lia).
all: try (clear - P3; unfold p_abeg; apply Z.mod_divide in P3; [|lia]; destruct P3 as [q Hq]; rewrite Hq;
replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat jB * ClassSize 24) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat jB) * 8192)
by (change (ClassSize 24) with 8192; ring); apply Z.mod_mul; lia).
all: try (clear - K9 K10; unfold r24, rb, kUserCap in *; lia).
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try exact ST6. all: try exact EF6.
all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL.
eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp.
- pose proof QR as (QT & _). cbn [ql lay refillΣ free_p] in QT. rewrite HQL in QT. rewrite HQL in QWF, Q1.
rewrite <- app_assoc in QWF. cbn [app] in QWF.
eapply evt_mono.
{ apply (qenq_miss_B_full_spec ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0x4a148) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
(Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) F fc m6 T (usp + -2056) M n SB lo
(Z.of_nat (length ([] ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb jf pre b0 ents0);
try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
all: try (clear - Hn1; lia). all: try (clear - MC1; lia). all: try (clear; cbn; lia).
all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
all: try (clear - T5; unfold SEGTOP_A in *; lia).
all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
all: try exact ST6. all: try exact QWF. all: try exact EF6.
all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL, <- app_assoc. cbn [app].
eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp. }
intros ms7 P7. destruct P7 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m7 & -> & MU7 & WM7 & MI7 & QR7 & NA7 & ST7).
rewrite (ret_pc_even 0x4a148) by (first [reflexivity | lia]).
destruct NA7 as (NA1 & NA2 & _).
assert (HSUB : sub_fp [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
(b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] W).
{ clear - Hsp. unfold W_E, qcacheT, pc_addr, cstat_alloc. solve_sub_fp. }
assert (PC7 : pclass_rep T 24 (ca_init Σb) [] m7).
{ rewrite Hinit. split.
- replace (Z.of_nat (length ([] ++ [Z.of_nat jB])) - 1) with (Z.of_nat (length (@nil Z))) in NA1 by (clear; cbn [length app]; lia).
change (ClassSize 24) with 8192. exact NA1.
- exists chs. split; [exact NA2|]. split; [exact Hlen|]. exact (firstn_snoc_map (cpw 24) [] (Z.of_nat jB) chs Hpre). }

assert (RP7 : rt_pres (live Σ2) (frames Σ1) usp m m7).
{ intros a Ha. rewrite (MU7 a).
- rewrite (MU6 a); [exact (RP5 a Ha)|].
assert (Hsp1 : l_ACEIL (lay Σ1) + 0x400 <= usp + -2208 + -64) by (cbn [lay free_p]; clear - Hsp; lia).
refine (kv_client Σ1 (W_R T SB 24 (ClassSize 24 * Z.of_nat (length (r_st (pr Σ1 24)))) (usp + -2208 + -64)) [] [] []
(usp + -2208 + -64) HG1 (rz_img Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_grant Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_slot Σ1 24 _ HG1 ltac:(lia) Hsp1)
(rz_shad_app Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_secmap Σ1 24 _ HG1 ltac:(lia) Hsp1) (rz_stack Σ1 24 _ HG1 ltac:(lia) Hsp1)
ltac:(apply Forall_forall; intros; exact I) (live Σ1) _ _ _).
+ intros p' n' Hin. pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
* left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
* right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []].
+ destruct Ha as [X|X]; [left; clear - X Hsp; lia | right; exact X].
- apply HSUB.
apply (kv_client Σb _ [(24, j0); (24, jB)] [] [] usp HG
(se_img Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_grant Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
(se_slot Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_shad_app Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
(se_secmap Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp) (se_stack Σb j0 jB st0 CkIdle usp HG Hj0 HjB' Hsp)
ltac:(apply Forall_forall; intros; exact I) (live Σb)); [|exact Ha].
intros p' n' Hin. pose proof HWb as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
intros [E|[E|[]]]; injection E as <- <-; [rewrite Hj0 in Hn'; injection Hn' as Est; destruct Hvar' as [(_ & X)|(X & _)]; rewrite X in Est; discriminate Est
| rewrite HjB' in Hn'; discriminate Hn'].
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
unfold enq_post. exists (Z_to_bv 64 0x4a148), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2056)),
(Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 (M + 16)), m7.
split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
split; [exact (new_ART_g Σb M n [] jB j0 st0 usp HWb HCA Hj0 Hvar' Hsp m6 m7 ART6 (munch_weaken _ _ _ _ HSUB MU7) WM7 QR7 PC7)|].
split; [exact WX|]. split; [exact WC|]. split; [exact MI7|]. split; [exact (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM5 WM6) WM7)|].
split; [rewrite Esp; rewrite (unsigned_lit (usp + -2208)) in ST7 by exact RSP; exact ST7|].
split; [rewrite Esp; exact RP7|].
split.
{ rewrite Esp. apply (icpt_frame_transport _ m6 m7 usp ra s0 s1 s2 s3 s4 s5 (icpt_frame_transport _ m5 m6 usp ra s0 s1 s2 s3 s4 s5 ICF MU6 WM6
ltac:(apply HWR; clear - Hsp; lia)) MU7 WM7). unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from].
clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
rewrite Esp. unfold qput_frame in FR5 |- *. apply (rw_cells_transport asegs _ m6 m7 _ _ (rw_cells_transport asegs _ m5 m6 _ _ FR5 MU6 WM6
ltac:(apply HWR; cbn [cells_size csize Nat.add]; clear - Hsp; lia)) MU7 WM7).
unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End MissG.
End RL_freeX.
Export RL_freeX.

Module RL_freeY.
Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0id X0i7 X0hz X0i3 X0i0 X0i1 X0i2 X0ge X0hs X0ie X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc X0e6 X0dd X0de X0dg X0di X0df X0dj X0dk X0dl X0dm X0dn X0do X0dp X0dq X0dx X0dy X0fd X0fc X0fe X0fi X0f7 X0c7 X0f4 X0g3.
Import RL_stmt RL_A2 RL_G RL_FH RL_freeV RL_freeW RL_freeX.

Definition enq_entry_st (usp T M n : Z) (gp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 M) (Z_to_bv 64 n) a5 a6 a7 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (T + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 qenq_entry) fc None m (seg_rom asegs).

Definition mfg_post (Σ1 : rtsA) (M n : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (jf : list byte),
ms = refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (bv_unsigned sp + -2208 + -64)) gp t0' t1' t2'
(Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) a4' a5' a6' a7'
(Z_to_bv 64 M) (Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (bv_unsigned sp + -2056))
(Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc (l_T (lay Σ1)) 24 m5
/\ ARTc Σ1 m5 /\ mem_inv asegs m5 /\ wmono asegs m m5 /\ stk asegs m5 lo (bv_unsigned sp + -2208 + -64)
/\ rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m5
/\ icpt_frame m5 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
/\ qput_frame m5 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46714)
s0 (Z_to_bv 64 (M + 16)) s2 s3
s4 s5 s6
/\ rw_cells asegs m5 (bv_unsigned sp + -2208 + -64)
[CB 8 jf; C8 (Z_to_bv 64 M); C8 (Z_to_bv 64 (l_T (lay Σ1) + 208));
C8 (Z_to_bv 64 (bv_unsigned sp + -2056)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (l_T (lay Σ1) + 80)); C8 (Z_to_bv 64 QUAR);
C8 (Z_to_bv 64 0x4a148)].

Lemma miss_front_g : forall (Σ1 : rtsA) (M n : Z) (m : mem) (j0 : nat)
(ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (F : bvmap 5 word) (fc : bv 32)
(m4 : mem) (lo : Z),
rt_wf0 Σ1 -> 1 <= n <= 2 ^ 27 -> l_ACEIL (lay Σ1) <= lo -> lo + 0x10000 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
ARTc Σ1 m4 -> mem_inv asegs m4 -> wmono asegs m m4 -> stk asegs m4 lo (bv_unsigned sp + -2208) ->
rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m4 -> icpt_frame m4 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5 ->
qput_frame m4 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46714)
s0 (Z_to_bv 64 (M + 16)) s2 s3
s4 s5 s6 ->
ca Σ1 24 = [] ->
(ql Σ1 = [] \/ exists pre ents0, nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch /\ ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents0)]
/\ length ents0 = 1021%nat) ->
evt asegs (mfg_post Σ1 M n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(enq_entry_st (bv_unsigned sp) (l_T (lay Σ1)) M n gp t0' t1' t2' a5' a6' a7' s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4).
Proof.
intros Σ1 M n m j0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
HW1 Hn1 HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 HCA0 Hvar0.
set (usp := bv_unsigned sp) in *.
pose proof (geo_of_wf0 Σ1 HW1) as HG1.
pose proof (g_grant Σ1 HG1 (l_T (lay Σ1)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
pose proof (se_disj Σ1 HG1) as (T5 & T4 & ATP). pose proof (fk_prb Σ1 HG1) as (FP1 & FP2 & FP3 & FP4 & FP5).
pose proof (fk_aceil Σ1 HG1) as (AC1 & AC2).
assert (Hsp : l_ACEIL (lay Σ1) + 0x10000 <= usp) by (clear - HLO HLO2; lia).
assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp AC1; unfold USTACK_TOP, SHB in *; lia).
pose proof ART4 as (CR4 & PR4 & CA4 & CH4 & SR4 & QR4 & DR4 & FS4 & IR4 & SH4 & VIS4).
pose proof (CA4 24 ltac:(lia)) as (PC24 & _). rewrite HCA0 in PC24. cbn [length Z.of_nat] in PC24.
pose proof QR4 as (QT4 & _).
eapply evt_cut.
{ unfold enq_entry_st. destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
- rewrite HQL in QT4.
apply (qenq_miss_A_empty_spec (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ1) + 80)) y3 y4 y5 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (l_T (lay Σ1) + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4
(l_T (lay Σ1)) (usp + -2056) M n lo _ _ QT4 PC24);
rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
+ clear - GT1. lia.
+ clear - T5. unfold SEGTOP_A in *. lia.
+ clear - GT3 HLO. lia.
+ exact ST4.
+ clear - HLO2. lia.
+ clear - Hsp Husp. unfold USTACK_TOP in *. lia.
+ exact MI4.
- rewrite HQL in QT4. pose proof (qwf_ql _ HW1) as QWF. rewrite HQL in QWF.
pose proof HW1 as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq, HQL in Q1.
eapply (qenq_miss_A_full_spec (Z_to_bv 64 0x4a148) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 QUAR)
(Z_to_bv 64 (l_T (lay Σ1) + 80)) y3 y4 y5 (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 (l_T (lay Σ1) + 208))
(Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4
(l_T (lay Σ1)) (usp + -2056) M n lo _ _ (l_SB (lay Σ1)) pre
(p_abeg (l_SB (lay Σ1)) 24 j0) ents0 HL0 QT4 QWF);
rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
+ eapply Z.le_lt_trans; [exact Q1 | reflexivity].
+ exact PC24.
+ clear - GT1. lia.
+ clear - T5. unfold SEGTOP_A in *. lia.
+ clear - GT3 HLO. lia.
+ clear - FP2 FP4 FP5 HLO. unfold r24. lia.
+ clear - FP4 FP5 ATP. unfold r24 in *. lia.
+ clear - FP1 FP4. lia.
+ exact ST4.
+ clear - HLO2. lia.
+ clear - Hsp Husp. unfold USTACK_TOP in *. lia.
+ exact MI4. }
intros ms P. destruct P as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & m5 & -> & MU5 & WM5 & MI5 & (jf & EF5) & ST5).
rewrite (unsigned_lit (usp + -2208)) in MU5, EF5, ST5 |- * by exact RSP.
apply evt_done.
pose proof HW1 as (_ & _ & _ & _ & (_ & _ & HBt & _) & _). pose proof HW1 as (_ & _ & _ & _ & _ & _ & _ & Dok1 & _).
assert (Ha : l_ACEIL (lay Σ1) <= usp + -2208 - 64) by (clear - Hsp; lia).
exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, m5, jf.
split; [reflexivity|].
split; [exact (ARTc_stack _ (usp + -2208 - 64) (usp + -2208) HG1 Ha m4 m5 ART4 MU5 WM5 HBt Dok1)|].
split; [exact MI5|]. split; [exact (wmono_trans asegs _ _ _ WM4 WM5)|].
split; [replace (usp + -2208 + -64) with (usp + -2208 - 64) by ring; exact ST5|].
split.
{ intros a Ha'. rewrite (MU5 a); [exact (RP4 a Ha')|].
refine (kv_client Σ1 [(usp + -2208 - 64, usp + -2208)] [] [] [] usp HG1
(sk_img _ _ _ HG1 Ha) (sk_grant _ _ _ HG1 Ha) (sk_slot _ _ _ HG1 Ha) (sk_shad_app _ _ _ HG1 Ha) (sk_secmap _ _ _ HG1 Ha) _
ltac:(apply Forall_forall; intros; exact I) (live Σ1) _ _ Ha').
- intros a' k' H1 H2. cbn [disjoint_from]. split; [clear - H1; lia | exact I].
- intros p' n' Hin. pose proof HW1 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
split.
{ apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). cbn [disjoint_from]. split; [clear; lia | exact I]. }
split.
{ unfold qput_frame in FR4 |- *. apply (rw_cells_transport asegs _ m4 m5 _ _ FR4 MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
split; [clear; lia | exact I]. }
replace (usp + -2208 + -64) with (usp + -2208 - 64) by ring. exact EF5.
Qed.

Lemma rt_eager_en : forall Σ cal jB M n, rt_eager (enq_new Σ cal jB M n) = rt_eager Σ.
Proof.
intros Σ cal jB M n. apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
cbn [enq_new set_ql pop24 pr]. destruct (Z.eqb_spec k' 24) as [->|_]; [|split; reflexivity]. unfold upd_reg. cbn [r_muser r_mfa]. split; reflexivity.
Qed.

Section Stage.
Variables (Σ Σ1 : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
(F : bvmap 5 word) (fc : bv 32) (m m4 : mem) (lo M n p : Z) (T : TSet).
Hypothesis DRAIN : drain_stmt.
Hypothesis FC : fixed_commit_node.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis HW1 : rt_wf0 Σ1.
Hypothesis HP : pend_e Σ1 M n.
Hypothesis EL : live Σ1 = live_remove p (live Σ).
Hypothesis EF : frames Σ1 = frames Σ.
Hypothesis ELY : lay Σ1 = lay Σ.
Hypothesis EC : credit Σ1 = credit Σ.
Hypothesis EPO : rtA_pois Σ1 = rtA_pois Σ.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x10000 <= bv_unsigned sp.
Hypothesis Husp : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis ART4 : ARTc Σ1 m4.
Hypothesis MI4 : mem_inv asegs m4.
Hypothesis WM4 : wmono asegs m m4.
Hypothesis ST4 : stk asegs m4 lo (bv_unsigned sp + -2208).
Hypothesis RP4 : rt_pres (live Σ1) (frames Σ1) (bv_unsigned sp) m m4.
Hypothesis ICF : icpt_frame m4 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5.
Hypothesis FR4 : qput_frame m4 (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ1) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46714)
s0 (Z_to_bv 64 (M + 16)) s2 s3
s4 s5 s6.
Hypothesis Hk : forall c', rl_postF Σ PMc F fc ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m c' -> realizes asegs c' T.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation entry := (enq_entry_st (bv_unsigned sp) (l_T (lay Σ1)) M n gp t0' t1' t2' a5' a6' a7' s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4).

Lemma es_n : 1 <= n <= 2 ^ 27.
Proof using HW1 HP. exact (pe_n Σ1 M n HW1 (proj1 HP)). Qed.

Lemma es_sp : l_ACEIL (lay Σ1) + 0x10000 <= usp.
Proof using ELY HLO HLO2. rewrite ELY. clear - HLO HLO2. lia. Qed.

Lemma es_fin : forall Σ2 c2, live Σ2 = live Σ1 -> frames Σ2 = frames Σ1 -> lay Σ2 = lay Σ1 -> credit Σ2 = credit Σ1 -> rtA_pois Σ2 = rtA_pois Σ1 ->
AST SEGTOP_A (rtA_allow Σ2) (enq_post Σ2 (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(fun mo => ARTM_A Σ2 mo /\ PMc mo) c2 -> realizes asegs c2 T.
Proof using DRAIN FDO MST EL EF ELY EC EPO HLO HLO2 Husp Hk.
intros Σ2 c2 E1 E2 E3 E4 E5 Hc2.
apply (fin_from_enq DRAIN Σ Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p T c2 FDO MST
ltac:(rewrite E1; exact EL) ltac:(rewrite E2; exact EF) ltac:(rewrite E3; exact ELY) ltac:(rewrite E4; exact EC) ltac:(rewrite E5; exact EPO)
HLO HLO2 Husp); [|exact Hk].
rewrite E1, <- EF. exact Hc2.
Qed.

Lemma es_new : forall (j0 : nat) cf,
(ql Σ1 = [] \/ exists pre ents0, nth_error (r_st (pr Σ1 24)) j0 = Some CkBatch /\ ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents0)]
/\ length ents0 = 1021%nat) ->
AST SEGTOP_A (rtA_allow Σ1) (eq entry) (fun mo => ARTM_A Σ1 mo /\ PMc mo) cf -> realizes asegs cf T.
Proof using DRAIN FC FDO MST HW1 HP EL EF ELY EC EPO HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk.
intros j0 cf Hvar0 Hc. pose proof es_n as Hn1. pose proof es_sp as Hsp. pose proof (geo_of_wf0 Σ1 HW1) as HG1.
pose proof (fk_aceil Σ1 HG1) as (AC1 & AC2).
assert (HLO1 : l_ACEIL (lay Σ1) <= lo) by (rewrite ELY; exact HLO).
pose proof HW1 as (_ & (_ & _ & R3 & _) & _). destruct (R3 24 ltac:(lia)) as (_ & _ & CAF).
destruct (ca Σ1 24) as [|x l] eqn:ECA.
-
assert (W1 : forall ms, eq entry ms -> evt asegs (mfg_post Σ1 M n ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
by (intros ms <-; exact (miss_front_g Σ1 M n m j0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
HW1 Hn1 HLO1 HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 ECA Hvar0)).
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
intros c1 Hc1.
apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1]. apply AST_exI in Hc1 as [y3 Hc1].
apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1]. apply AST_exI in Hc1 as [y7 Hc1].
apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [y10 Hc1].
apply AST_exI in Hc1 as [m5 Hc1]. apply AST_exI in Hc1 as [jf Hc1].
pose proof Hc1 as (_ & (_ & ART5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5 & EF5) & _ & _).
assert (RSP : 0 <= usp + -2208 + -64 < 2 ^ 64) by (clear - Hsp Husp AC1; unfold USTACK_TOP, SHB in *; lia).
pose proof (pend_room_e Σ1 M n HW1 HP ECA) as HROOM.

pose proof HW1 as (_ & (HR1 & _) & _).
pose proof (refill_ca_len (pr Σ1 24) 24 ltac:(clear; lia) (HR1 24 ltac:(clear; lia))) as LCA.
change (MaxCount 24 / 2) with 1 in LCA.
pose proof (refill_wf0 Σ1 24 ltac:(clear; lia) HW1 ECA HROOM) as HWb.
pose proof HWb as (_ & (_ & _ & HR3 & _) & _). destruct (HR3 24 ltac:(clear; lia)) as (_ & _ & CAFb).
cbn [refillΣ ca] in CAFb. rewrite Z.eqb_refl in CAFb.
destruct (refill_ca (pr Σ1 24) 24) as [|xb [|yb lb]] eqn:ECAb; [cbn in LCA; lia | | cbn in LCA; lia].
pose proof (proj1 (Forall_forall _ _) CAFb xb (in_eq xb [])) as (Hxb & _).
set (jB := Z.to_nat xb).
assert (HjB : refill_ca (pr Σ1 24) 24 = [Z.of_nat jB]) by (rewrite ECAb; unfold jB; rewrite Z2Nat.id by (clear - Hxb; lia); reflexivity).
assert (Hc1' : AST SEGTOP_A (rtA_allow Σ1)
(eq (refill_entry_st (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp y0 y1 y2
(Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) y3 y4 y5 y6
(Z_to_bv 64 M) (Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056))
(Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 y7 y8 y9 y10 F fc (l_T (lay Σ1)) 24 m5))
(fun mo => ARTM_A Σ1 mo /\ PMc mo) c1).
{ eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E | intros mo X; exact X]. }
apply (refill_core Σ1 PMc m5 24 lo (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp
(Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) (Z_to_bv 64 M)
(Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 F fc
y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 FDO MST HW1 ART5 ltac:(clear; lia) ECA HROOM MI5
ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; exact ST5) HLO1
ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; clear - HLO2; lia)
ltac:(rewrite (unsigned_lit (usp + -2208 + -64)) by exact RSP; clear - Husp; unfold USTACK_TOP in *; lia) FC T c1 Hc1').
intros c2 Hc2.
assert (VAR : exists (jX : nat) (stX : ckst), nth_error (r_st (pr (refillΣ Σ1 24) 24)) jX = Some stX
/\ ((jX = jB /\ stX = CkIdle /\ ql Σ1 = [])
\/ (stX = CkBatch /\ exists pre ents0, ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 jX, ents0)] /\ length ents0 = 1021%nat))).
{ destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
- exists jB, CkIdle. split; [|left; split; [reflexivity|]; split; [reflexivity | exact HQL]].
exact (ng_jB _ [] jB HWb ltac:(cbn [refillΣ ca]; rewrite Z.eqb_refl; exact HjB)).
- exists j0, CkBatch. split; [|right; split; [reflexivity|]; exists pre, ents0; split; [exact HQL | exact HL0]].
exact (rfs_keep Σ1 24 ltac:(clear; lia) HW1 24 j0 _ Hj0). }
destruct VAR as (jX & stX & HjX & HvarX).
assert (W2 : forall ms, rf_post F fc Σ1 24 lo (Z_to_bv 64 qenq_refill_ret) (Z_to_bv 64 (usp + -2208 + -64)) gp
(Z_to_bv 64 (pc_addr (l_T (lay Σ1)) 24)) (Z_to_bv 64 (cacheT (l_T (lay Σ1)))) (Z_to_bv 64 M)
(Z_to_bv 64 (qcacheT (l_T (lay Σ1)))) (Z_to_bv 64 (usp + -2056)) (Z_to_bv 64 n) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 m5 ms ->
evt asegs (fun ms' =>
enq_post (enq_new (refillΣ Σ1 24) [] jB M n) (live Σ1) (frames Σ1)
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms') ms).
{ intros ms (m6 & RET & ART6 & MI6 & WM6 & ST6 & MU6).
destruct RET as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & ->).
rewrite (ret_pc_even qenq_refill_ret) by (unfold qenq_refill_ret; first [reflexivity | lia]).
rewrite (unsigned_lit (usp + -2208 + -64)) in ST6, MU6 by exact RSP.
eapply evt_mono; [apply (miss_enq_g Σ1 M n m jB jX stX usp HW1 HP ECA Hsp HjB HjX HvarX
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m5 m6 lo jf (Z_to_bv 64 qenq_refill_ret)
z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 eq_refl HLO1 HLO2 Husp WM5 RP5 ICF5 FR5 EF5 ART6 MI6 WM6 ST6 MU6)|].
intros ms' P. exact P. }
apply (cps_realizes asegs _ _ _ c2 (ast_evt asegs SEGTOP_A asegs_wx asegs_below _ _ _ _ (fl_ASTA_mat_stable _ PMc MST) W2) Hc2).
intros c3 Hc3.
apply (es_fin (enq_new (refillΣ Σ1 24) [] jB M n) c3 eq_refl eq_refl eq_refl eq_refl eq_refl).
eapply AST_conseq; [exact Hc3 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
apply (artm_eq (refillΣ Σ1 24)); [reflexivity | reflexivity | exact (rt_eager_en _ [] jB M n) | exact HM].
-
destruct (exists_last (l := x :: l) ltac:(discriminate)) as (cal & xj & Ecal).
pose proof (proj1 (Forall_forall _ _) CAF xj ltac:(rewrite Ecal; apply in_or_app; right; left; reflexivity)) as (Hxj & _).
set (jB := Z.to_nat xj).
assert (HCA : ca Σ1 24 = cal ++ [Z.of_nat jB]) by (rewrite ECA, Ecal; unfold jB; rewrite Z2Nat.id by (clear - Hxj; lia); reflexivity).
assert (VAR : exists (jX : nat) (stX : ckst), nth_error (r_st (pr Σ1 24)) jX = Some stX
/\ ((jX = jB /\ stX = CkIdle /\ ql Σ1 = [])
\/ (stX = CkBatch /\ exists pre ents0, ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 jX, ents0)] /\ length ents0 = 1021%nat))).
{ destruct Hvar0 as [HQL|(pre & ents0 & Hj0 & HQL & HL0)].
- exists jB, CkIdle. split; [exact (ng_jB Σ1 cal jB HW1 HCA)|]. left. split; [reflexivity|]. split; [reflexivity | exact HQL].
- exists j0, CkBatch. split; [exact Hj0|]. right. split; [reflexivity|]. exists pre, ents0. split; [exact HQL | exact HL0]. }
destruct VAR as (jX & stX & HjX & HvarX).
assert (W1 : forall ms, eq entry ms ->
evt asegs (enq_post (enq_new Σ1 cal jB M n) (live Σ1) (frames Σ1) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
by (intros ms <-; exact (new_enq_g Σ1 M n m cal jB jX stX usp HW1 HP HCA HjX HvarX Hsp
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
eq_refl ART4 MI4 WM4 ST4 HLO1 HLO2 Husp RP4 ICF FR4)).
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
intros c1 Hc1. apply (es_fin (enq_new Σ1 cal jB M n) c1 eq_refl eq_refl eq_refl eq_refl eq_refl).
eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
apply (artm_eq Σ1); [reflexivity | reflexivity | exact (rt_eager_en Σ1 cal jB M n) | exact HM].
Qed.

Theorem enq_stage : forall cf, AST SEGTOP_A (rtA_allow Σ1) (eq entry) (fun mo => ARTM_A Σ1 mo /\ PMc mo) cf -> realizes asegs cf T.
Proof using DRAIN FC FDO MST HW1 HP EL EF ELY EC EPO HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk.
intros cf Hc. pose proof es_n as Hn1. pose proof es_sp as Hsp.
pose proof HW1 as (_ & _ & _ & _ & (_ & _ & QB & _ & Q5 & _) & _).
destruct (ql Σ1) as [|b l] eqn:EQL; [exact (es_new 0 cf (or_introl EQL) Hc)|].
destruct (exists_last (l := b :: l) ltac:(discriminate)) as (pre & (b0 & ents) & Eql).
destruct (proj1 (Forall_forall _ _) QB (b0, ents) ltac:(rewrite Eql; apply in_or_app; left; apply in_or_app; right; left; reflexivity))
as (j0 & Hj0 & Eb0). cbn [fst] in Eb0.
assert (HQL : ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents)]) by (rewrite EQL, Eql, Eb0; reflexivity).
pose proof (proj1 (Forall_forall _ _) Q5 (b0, ents) ltac:(rewrite Eql; apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as HL5.
cbn [snd] in HL5.
destruct (Nat.lt_ge_cases (length ents) 1021) as [HL|HL].
-
assert (W1 : forall ms, eq entry ms ->
evt asegs (enq_post (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])) (live Σ1) (frames Σ1)
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
by (intros ms <-; exact (app_enq_g Σ1 M n m pre j0 ents usp HW1 HP HQL Hj0 HL Hsp
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
eq_refl ART4 MI4 WM4 ST4 ltac:(rewrite ELY; exact HLO) HLO2 Husp RP4 ICF FR4)).
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST) W1) Hc).
intros c1 Hc1. apply (es_fin (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])) c1 eq_refl eq_refl eq_refl eq_refl eq_refl).
eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP'). split; [|exact HP'].
apply (artm_eq Σ1); [reflexivity | reflexivity | reflexivity | exact HM].
-
apply (es_new j0 cf); [|exact Hc]. right. exists pre, ents. split; [exact Hj0|]. split; [exact HQL | clear - HL HL5; lia].
Qed.

End Stage.
End RL_freeY.
Export RL_freeY.
