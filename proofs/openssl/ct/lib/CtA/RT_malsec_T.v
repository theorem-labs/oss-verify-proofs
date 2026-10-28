(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState ITree Nodes. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_sec_defs R_asan_defs R_allocate1 R_allocate2 R_allocate3 R_allocate3L R_asan_malloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_icfacts RT_malstate RT_freestate RT_maltail RT_malcore_stmt RT_sys_stmt RT_vis RT_malsec_state RT_malsec_front RT_malsec_front2 RT_malsec_rev RT_malsec_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hidep (X : Prop) : Prop := X.
Lemma hidep_of : forall X : Prop, X -> hidep X. Proof. intros X H. exact H. Qed.

Section STail.
Variables (Σ : rtsA) (mA m2 : mem) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word) (F : bvmap 5 word)
  (fc : bv 32) (n lo P : Z) (tr : list Z) (j0 : list byte).
Hypothesis Hn : 64512 < n <= 0x8000000.
Hypothesis HA : ART_A Σ mA.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 2144 <= USTACK_TOP.
Hypothesis SPA : B mod 16 = 0.
Hypothesis Htr : In tr T_MAIN.
Hypothesis Htrl : (1 <= length tr <= TR_MAX)%nat.
Hypothesis MU1 : munch (W_1 Σ B n P) mA m2.
Hypothesis WM1 : wmono ctasegs mA m2.
Hypothesis SKM : stk ctasegs m2 P (P + smsz n).
Hypothesis SST : stk ctasegs m2 (shad P) (shad (P + smsz n)).
Hypothesis HDR : shdr m2 P (smsz n) (needed2 n) (Z.of_nat (length (sec Σ))).

#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation PAB := (l_PAB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation msz := (smsz n).
#[local] Notation SZ := (needed2 n).
#[local] Notation AB := (P + 4096).
#[local] Notation S := (smsz n - 4096).
#[local] Notation D := (dep Σ).
#[local] Notation BK := (DEP_BK (hash_of (d_hs (dep Σ)) 1)).

(* [comment removed for export] *)
Definition W_T : list ivl :=
  [(AB, P + msz); (shad AB, shad (P + msz)); (T + 2768, T + 3168); (0x743f08, 0xb53f30); (DNB, DNB + 2 ^ 20);
   (SSB, SSB + 2 ^ 23); (l_ACEIL L, B + -16)].

(* [comment removed for export] *)
Definition W_S : list ivl :=
  [(P, P + msz); (shad P, shad (P + msz)); (T + 2768, T + 3168); (INST + 0x70, INST + 0x2d0); (0x743f08, 0xb53f30);
   (DNB, DNB + 2 ^ 20); (SSB, SSB + 2 ^ 23); (PAB, PAB + 0x20000); (l_ACEIL L, B + -16)].

(* [comment removed for export] *)
Definition sl_facts (m : mem) : Prop :=
  ahdr m (AB + 2032) n /\ lch m AB (AB + 2032)
  /\ bytes_at ctasegs m (shad (AB + 2048)) (ushadow n)
  /\ bytes_at ctasegs m (shad AB) (farun (2048 / 8))
  /\ bytes_at ctasegs m (shad (AB + 2048 + ru8 n)) (farun ((S - 2048 - ru8 n) / 8))
  /\ depot_rep (fst (depot_put D tr)) BK DNB SSB m.

Definition sl_post : machine_state -> Prop :=
  fun ms => exists m', ret_st (Z_to_bv 64 0x19bcec) (Z_to_bv 64 (B + -16)) gp (Z_to_bv 64 tpA) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A
                         s10A s11A (Z_to_bv 64 (AB + 2048)) m' ms
    /\ munch W_T m2 m' /\ wmono ctasegs m2 m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (B + -16) /\ sl_facts m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sl_sizes : rz_size n = 2048 /\ from_primary n = false /\ needed2 n = ru8 n + 4096 /\ 65536 < SZ /\ SZ mod 8 = 0
  /\ sa_msz SZ = msz /\ sec_ru n = S /\ n <= ru8 n < n + 8 /\ ru8 n mod 8 = 0 /\ Z.of_nat (length (ushadow n)) = ru8 n / 8
  /\ size_rd n mod 8 = 0 /\ size_rd n <= n < size_rd n + 8 /\ 8 <= size_rd n.
Proof using Hn. clear - Hn.
  pose proof (rz_size_big n ltac:(lia)) as RZ. pose proof (msec_size n Hn) as (K1 & K2 & K3 & K4).
  pose proof (smsz_sa n Hn) as (E1 & E2 & E3). pose proof (size_rd_facts n ltac:(lia)) as (D1 & D2 & D3).
  assert (RD : rounded n = ru8 n) by (unfold rounded, ru8; rewrite !Z.max_l by lia; reflexivity).
  assert (N2 : needed2 n = ru8 n + 4096) by (unfold needed2, needed; rewrite K4, RZ, RD; lia).
  split; [exact RZ|]. split; [exact K4|]. split; [exact N2|]. split; [exact K1|]. split; [exact K2|]. split; [symmetry; exact E1|].
  split; [unfold sec_ru; rewrite E1; unfold sa_msz, roundup4k; lia|].
  split; [unfold ru8; Z.div_mod_to_equations; lia|]. split; [unfold ru8; rewrite Z.mul_comm; apply Z.mod_mul; lia|].
  split; [exact (ushadow_len n ltac:(lia))|]. split; [exact D1|]. split; [lia|].
  unfold size_rd. assert (1 <= n / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma sl_geo :
  SEGTOP_A <= P /\ P mod 4096 = 0 /\ P + msz <= l_ACEIL L /\ 72704 <= msz /\ msz mod 4096 = 0 /\ msz <= 0x8004000
  /\ 2 ^ 44 + SHB + 8 <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ B + 2144 <= 2 ^ 47 /\ kHighShadowEnd + 8 <= lo
  /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ SEGTOP_A <= TCX /\ TCX + 0x10000 <= l_ACEIL L
  /\ SEGTOP_A <= PAB /\ PAB + 0x800000 <= l_ACEIL L /\ SEGTOP_A <= DNB /\ DNB + 2 ^ 20 <= l_ACEIL L
  /\ SEGTOP_A <= SSB /\ SSB + 2 ^ 23 <= l_ACEIL L /\ 0 < SB /\ SB + 2 ^ 37 <= l_ACEIL L.
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  pose proof (sb_geo Σ mA B n lo P Hn HA LOW LOR SPT HG) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14
                                                          & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21).
  pose proof (geo_grant Σ mA HA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as (D1 & _ & D3 & _ & D5).
  pose proof (geo_grant Σ mA HA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as (B1 & _ & B3 & _ & B5).
  pose proof (geo_prb Σ mA HA) as (P1 & P2 & P3).
  pose proof (geo_grant Σ mA HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _ & G5).
  assert (D5' : SEGTOP_A <= DNB) by (clear - D1 D5; unfold SEGTOP_A in *; destruct D5; lia).
  assert (B5' : SEGTOP_A <= SSB) by (clear - B1 B5; unfold SEGTOP_A in *; destruct B5; lia).
  clear D5 B5 G5.
  repeat split; try assumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma sl_apart :
  apart P msz T 4096 /\ apart P msz TCX 0x10000 /\ apart P msz DNB 0x100000 /\ apart P msz SSB 0x800000
  /\ apart P msz (l_PRB L) 0x2000011000 /\ apart P msz PAB 0x800000
  /\ apart T 4096 TCX 0x10000 /\ apart T 4096 DNB 0x100000 /\ apart T 4096 SSB 0x800000 /\ apart TCX 0x10000 DNB 0x100000
  /\ apart TCX 0x10000 SSB 0x800000 /\ apart DNB 0x100000 SSB 0x800000
  /\ apart PAB 0x800000 T 4096 /\ apart PAB 0x800000 TCX 0x10000 /\ apart PAB 0x800000 DNB 0x100000 /\ apart PAB 0x800000 SSB 0x800000
  /\ (DNB + 0x100000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= DNB) /\ (SSB + 0x800000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= SSB)
  /\ (P + msz <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= P) /\ (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T)
  /\ (TCX + 0x10000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= TCX) /\ (PAB + 0x800000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= PAB)
  /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T).
Proof using Hn HA HG. clear - Hn HA HG.
  pose proof (rv_grant_apart Σ mA P n HA HG) as GA.
  pose proof (rv_map Σ mA P n HA HG Hn) as (_ & _ & _ & M4 & _).
  pose proof (geo_apart Σ mA HA 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23. pose proof (geo_apart Σ mA HA 2 6 _ _ ltac:(lia) eq_refl eq_refl) as A26.
  pose proof (geo_apart Σ mA HA 2 7 _ _ ltac:(lia) eq_refl eq_refl) as A27. pose proof (geo_apart Σ mA HA 3 6 _ _ ltac:(lia) eq_refl eq_refl) as A36.
  pose proof (geo_apart Σ mA HA 3 7 _ _ ltac:(lia) eq_refl eq_refl) as A37. pose proof (geo_apart Σ mA HA 6 7 _ _ ltac:(lia) eq_refl eq_refl) as A67.
  pose proof (geo_apart Σ mA HA 1 2 _ _ ltac:(lia) eq_refl eq_refl) as A12. pose proof (geo_apart Σ mA HA 1 3 _ _ ltac:(lia) eq_refl eq_refl) as A13.
  pose proof (geo_apart Σ mA HA 1 6 _ _ ltac:(lia) eq_refl eq_refl) as A16. pose proof (geo_apart Σ mA HA 1 7 _ _ ltac:(lia) eq_refl eq_refl) as A17.
  pose proof (geo_grant Σ mA HA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as (_ & _ & _ & D4 & _).
  pose proof (geo_grant Σ mA HA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as (_ & _ & _ & B4 & _).
  pose proof (geo_grant Σ mA HA T 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (_ & _ & _ & T4 & T5).
  pose proof (geo_grant Σ mA HA TCX 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity)) as (_ & _ & _ & X4 & _).
  pose proof (geo_grant Σ mA HA PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (_ & _ & _ & P4 & _).
  cbn [fst snd] in *.
  split; [exact (GA T 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity))|].
  split; [exact (GA TCX 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity))|].
  split; [exact (GA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity))|].
  split; [exact (GA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity))|].
  split; [exact (GA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity))|].
  split; [exact (GA PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity))|].
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with X : _ \/ _ |- _ => clear X end.
Ltac sl_sep := clear_disj; first
  [ unfold SHB, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SEGTOP_A in *; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X);
    unfold SEGTOP_A, SHB in *; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof sl_apart as (_ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia ].

Lemma ru8_sd : forall k, 0 <= k -> (k mod 8 <> 0 -> size_rd k / 8 + 1 = ru8 k / 8) /\ (k mod 8 = 0 -> size_rd k = ru8 k).
Proof using. intros k Hk. clear - Hk. unfold size_rd, ru8. split; intros Hm; Z.div_mod_to_equations; lia. Qed.

(* [comment removed for export] *)
Lemma sl_room : ru8 n + 8192 <= msz /\ n + 6144 < msz.
Proof using Hn. clear - Hn.
  pose proof sl_sizes as (Z1 & _ & _ & _ & _ & _ & _ & Z8 & _).
  assert (SR : ru8 n + 4096 + 4096 <= msz).
  { clear - Hn Z1. unfold smsz, pg_up. rewrite Z1. unfold needed, rounded. rewrite !Z.max_l by lia. rewrite Z1. unfold ru8.
    Z.div_mod_to_equations. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma sl_shad : shad AB = shad P + 512 /\ shad (P + msz) = shad P + msz / 8 /\ SHB <= shad P /\ shad (P + msz) <= 2 ^ 44 + SHB
  /\ shad (AB + 2048) = shad AB + 256 /\ shad (AB + 2048 + ru8 n) = shad AB + 256 + ru8 n / 8
  /\ shad (AB + 2048 + size_rd n) = shad AB + 256 + size_rd n / 8 /\ 256 + ru8 n / 8 <= S / 8 /\ size_rd n / 8 <= ru8 n / 8
  /\ (n mod 8 <> 0 -> size_rd n / 8 + 1 = ru8 n / 8) /\ (n mod 8 = 0 -> size_rd n = ru8 n)
  /\ (S - 2048 - ru8 n) / 8 = S / 8 - 256 - ru8 n / 8 /\ 0 <= (S - 2048 - ru8 n) / 8 /\ S / 8 = msz / 8 - 512
  /\ shad AB + S / 8 = shad (P + msz) /\ (AB + 2048) mod 8 = 0.
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  pose proof sl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
  pose proof sl_sizes as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13).
  pose proof (rv_shad Σ mA P n HA HG Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  assert (P8 : P mod 8 = 0) by (apply (mod8_of P 4096); [lia | exact G2 | exists 512; reflexivity]).
  assert (M8 : msz mod 8 = 0) by (apply (mod8_of msz 4096); [lia | exact G5 | exists 512; reflexivity]).
  assert (E1 : shad AB = shad P + 512) by (rewrite (shad_add8 P 4096 P8 eq_refl); reflexivity).
  assert (AB8 : AB mod 8 = 0) by (rewrite Z.add_mod, P8 by lia; reflexivity).
  assert (E2 : shad (AB + 2048) = shad AB + 256) by (rewrite (shad_add8 AB 2048 AB8 eq_refl); reflexivity).
  assert (E3 : shad (AB + 2048 + ru8 n) = shad AB + 256 + ru8 n / 8).
  { replace (AB + 2048 + ru8 n) with (AB + (2048 + ru8 n)) by ring.
    rewrite (shad_add8 AB (2048 + ru8 n) AB8 ltac:(rewrite Z.add_mod, Z9 by lia; reflexivity)).
    destruct (sb_div8 2048 (ru8 n) eq_refl Z9) as (X & _). rewrite X. change (2048 / 8) with 256. ring. }
  assert (E4 : shad (AB + 2048 + size_rd n) = shad AB + 256 + size_rd n / 8).
  { replace (AB + 2048 + size_rd n) with (AB + (2048 + size_rd n)) by ring.
    rewrite (shad_add8 AB (2048 + size_rd n) AB8 ltac:(rewrite Z.add_mod, Z11 by lia; reflexivity)).
    destruct (sb_div8 2048 (size_rd n) eq_refl Z11) as (X & _). rewrite X. change (2048 / 8) with 256. ring. }
  assert (E5 : S / 8 = msz / 8 - 512) by (destruct (sb_div8 msz 4096 M8 eq_refl) as (_ & X); rewrite X; reflexivity).
  pose proof sl_room as (SR & _).
  split; [exact E1|]. split; [exact S2|]. split; [exact S5|]. split; [unfold K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
  assert (Hr8 : ru8 n / 8 * 8 = ru8 n) by (rewrite Z.mul_comm; symmetry; apply Z.div_exact; lia).
  assert (Hs8 : size_rd n / 8 * 8 = size_rd n) by (rewrite Z.mul_comm; symmetry; apply Z.div_exact; lia).
  assert (Hm8 : msz / 8 * 8 = msz) by (rewrite Z.mul_comm; symmetry; apply Z.div_exact; lia).
  split; [lia|]. split; [lia|].
  pose proof (ru8_sd n ltac:(lia)) as (RS1 & RS2).
  split; [exact RS1|]. split; [exact RS2|].
  assert (E6 : (S - 2048 - ru8 n) / 8 = S / 8 - 256 - ru8 n / 8).
  { replace (S - 2048 - ru8 n) with (msz - (6144 + ru8 n)) by ring.
    destruct (sb_div8 msz (6144 + ru8 n) M8 ltac:(rewrite Z.add_mod, Z9 by lia; reflexivity)) as (_ & X). rewrite X, E5.
    destruct (sb_div8 6144 (ru8 n) eq_refl Z9) as (Y & _). rewrite Y. change (6144 / 8) with 768. ring. }
  split; [exact E6|]. split; [rewrite E6, E5; lia|]. split; [exact E5|]. split; [rewrite E1, E5, S2; ring|].
  rewrite Z.add_mod, AB8 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sl_map_vs_shad : forall a k, P <= a -> a + k <= P + msz -> forall x y, shad P <= x -> y <= shad (P + msz) -> a + k <= x \/ y <= a.
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  intros a k H1 H2 x y X1 X2. pose proof sl_shad as (_ & _ & H3 & H4 & _).
  pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X19 & _).
  clear - H1 H2 X1 X2 H3 H4 X19. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. destruct X19; lia.
Qed.

Lemma sl_shad_vs_T : forall x y, shad P <= x -> y <= shad (P + msz) -> forall a k, T <= a -> a + k <= T + 4096 -> a + k <= x \/ y <= a.
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  intros x y X1 X2 a k H1 H2. pose proof sl_shad as (_ & _ & H3 & H4 & _).
  pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X20 & _).
  clear - H1 H2 X1 X2 H3 H4 X20. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. destruct X20; lia.
Qed.

Lemma sl_map_vs_T : forall a k, P <= a -> a + k <= P + msz -> forall b j, T <= b -> b + j <= T + 4096 -> a + k <= b \/ b + j <= a.
Proof using Hn HA HG. clear - Hn HA HG.
  intros a k H1 H2 b j B1 B2. pose proof sl_apart as (X1 & _). unfold apart in X1. clear - H1 H2 B1 B2 X1. destruct X1; lia.
Qed.

(* [comment removed for export] *)
Lemma sl_objs : (TCX + 0xa0 <= 0x7fff7000 \/ 0x10007fff8000 <= TCX) /\ (TCX + 0xa0 <= 0x10000 \/ 0xbcb000 <= TCX)
  /\ (T + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= T) /\ (T + 4096 <= 0x10000 \/ 0xbcb000 <= T).
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  pose proof sl_geo as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G13 & _).
  pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X20 & X21 & _ & X23).
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *.
  split; [clear - X21; destruct X21; [left | right]; lia|]. split; [right; lia|].
  split; [clear - X20; destruct X20; [left | right]; lia | exact X23].
Qed.

(* [comment removed for export] *)
Definition kinds (x y : Z) : Prop :=
  (P <= x /\ y <= P + msz) \/ (shad P <= x /\ y <= shad (P + msz)) \/ (T <= x /\ y <= T + 4096) \/ (l_ACEIL L <= x /\ y <= B + -16)
  \/ (0x10000 <= x /\ y <= 0x743f08) \/ (PAB <= x /\ y <= PAB + 0x800000).

Lemma sl_kind_dep : forall x y, kinds x y ->
  (forall a k, 0x743f08 <= a -> a + k <= 0xb53f30 -> a + k <= x \/ y <= a)
  /\ (forall a k, DNB <= a -> a + k <= DNB + 2 ^ 20 -> a + k <= x \/ y <= a)
  /\ (forall a k, SSB <= a -> a + k <= SSB + 2 ^ 23 -> a + k <= x \/ y <= a).
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  intros x y Hk. pose proof sl_geo as (G1 & _ & G3 & _ & _ & _ & G7 & G8 & G9 & _ & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & _).
  pose proof sl_shad as (_ & _ & H3 & H4 & _).
  unfold kinds, SEGTOP_A, SHB in *.
  destruct Hk as [C|[C|[C|[C|[C|C]]]]].
  - pose proof sl_apart as (_ & _ & X3 & X4 & _). unfold apart in X3, X4.
    split; [intros a k A1 A2; lia|]. split; intros a k A1 A2; [clear - C A1 A2 X3; destruct X3; lia | clear - C A1 A2 X4; destruct X4; lia].
  - pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & X18 & _).
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in X17, X18.
    split; [intros a k A1 A2; lia|]. split; intros a k A1 A2; [clear - C A1 A2 X17 H3 H4; destruct X17; lia | clear - C A1 A2 X18 H3 H4; destruct X18; lia].
  - pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & X8 & X9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X23).
    unfold apart in X8, X9. unfold SEGTOP_A in X23.
    split; [intros a k A1 A2; clear - C A1 A2 X23; destruct X23; lia|].
    split; intros a k A1 A2; [clear - C A1 A2 X8; destruct X8; lia | clear - C A1 A2 X9; destruct X9; lia].
  - split; [intros a k A1 A2; lia|]. split; intros a k A1 A2; lia.
  - split; [intros a k A1 A2; lia|]. split; intros a k A1 A2; lia.
  - pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X15 & X16 & _). unfold apart in X15, X16.
    split; [intros a k A1 A2; lia|]. split; intros a k A1 A2; [clear - C A1 A2 X15; destruct X15; lia | clear - C A1 A2 X16; destruct X16; lia].
Qed.

(* [comment removed for export] *)
Lemma sl_dep_avoid : forall W, Forall (fun p => kinds (fst p) (snd p)) W ->
  disjoint_from W d_tab (d_nuniq + 4 - d_tab) /\ disjoint_from W d_map1 8 /\ disjoint_from W DNB (2 ^ 20)
  /\ disjoint_from W s_total 8 /\ disjoint_from W s_data0 (s_stored0 + 4 - s_data0) /\ disjoint_from W SSB (2 ^ 23).
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  induction W as [|[x y] W IH]; intros HF; [repeat split; exact I|].
  apply Forall_cons_iff in HF as [Hp HF]. specialize (IH HF). destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
  destruct (sl_kind_dep x y Hp) as (D1 & D2 & D3). cbn [disjoint_from].
  split; [split; [apply D1; lia | exact I1]|]. split; [split; [apply D1; lia | exact I2]|]. split; [split; [apply D2; lia | exact I3]|].
  split; [split; [apply D1; lia | exact I4]|]. split; [split; [apply D1; lia | exact I5]|]. split; [apply D3; lia | exact I6].
Qed.

(* [comment removed for export] *)
Lemma sl_map_avoid_WT : forall a k, P <= a -> a + k <= AB -> disjoint_from W_T a k.
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  intros a k H1 H2. pose proof sl_geo as (G1 & _ & G3 & G4 & _ & _ & G7 & G8 & G9 & _ & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & _).
  pose proof sl_shad as (H3 & H4 & H5 & H6 & _).
  pose proof (sl_map_vs_shad a k ltac:(lia) ltac:(lia) (shad AB) (shad (P + msz)) ltac:(lia) ltac:(lia)) as Y1.
  pose proof (sl_map_vs_T a k ltac:(lia) ltac:(lia) (T + 2768) 400 ltac:(lia) ltac:(lia)) as Y2.
  pose proof sl_apart as (_ & _ & X3 & X4 & _). unfold apart in X3, X4.
  unfold W_T. cbn [disjoint_from]. unfold SEGTOP_A in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [clear - X3 H1 H2 G4; destruct X3; lia|].
  split; [clear - X4 H1 H2 G4; destruct X4; lia|]. split; [lia | exact I].
Qed.

Ltac kinds_tac := cbv beta; cbn [fst snd];
  lazymatch goal with |- kinds ?x ?y =>
    unfold kinds;
    first [ lazymatch x with context [shad] => right; left; split; lia end
          | lazymatch x with context [l_T] => right; right; left; split; lia end
          | lazymatch y with context [B] => right; right; right; left; split; lia end
          | left; split; lia | right; right; right; right; left; split; lia | right; right; right; right; right; split; lia ] end.
Ltac dep_frame DR OK MU WM := let X := fresh in
  lazymatch type of MU with munch ?W _ _ =>
    assert (X : Forall (fun p => kinds (fst p) (snd p)) W) by (repeat (apply Forall_cons; [kinds_tac|]); apply Forall_nil);
    let Y := fresh in pose proof (sl_dep_avoid W X) as Y;
    exact (depot_rep_frame _ _ _ _ _ _ _ _ DR OK MU WM (proj1 Y) (proj1 (proj2 Y)) (proj1 (proj2 (proj2 Y)))
             (proj1 (proj2 (proj2 (proj2 Y)))) (proj1 (proj2 (proj2 (proj2 (proj2 Y))))) (proj2 (proj2 (proj2 (proj2 (proj2 Y))))))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sl_mS : forall (m : mem), munch W_T m2 m -> munch W_S mA m.
Proof using Hn HA HG LOW LOR SPT MU1. clear - Hn HA HG LOW LOR SPT MU1.
  intros m MU. pose proof sl_geo as (G1 & G2 & G3 & _ & _ & _ & G7 & G8 & G9 & _ & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & _).
  pose proof sl_shad as (H1 & H2 & H3 & H4 & _).
  apply (munch_trans _ mA m2 m).
  - eapply munch_weaken; [|exact MU1]. unfold W_1, W_1s, W_S. sfp.
  - eapply munch_weaken; [|exact MU]. unfold W_T, W_S. sfp.
Qed.

Lemma sw_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> (a + k <= INST + 0x70 \/ INST + 0x2d0 <= a) ->
  (a + k <= 0x743f08 \/ 0xb53f30 <= a) -> disjoint_from W_S a k.
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  intros a k H1 H2 H3 H4. pose proof sl_geo as (G1 & _ & G3 & _ & _ & _ & G7 & G8 & G9 & _ & G11 & G12 & G13 & G14 & G15 & G16 & G17
                                                 & G18 & G19 & G20 & _).
  pose proof sl_shad as (_ & _ & S3 & S4 & _).
  pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X23).
  unfold W_S. cbn [disjoint_from]. unfold SEGTOP_A, SHB, INST, g_instance in *.
  split; [lia|]. split; [lia|]. split; [clear - X23 H1 H2; destruct X23; lia|]. split; [exact H3|]. split; [exact H4|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia | exact I].
Qed.

Lemma sw_T : forall a k, T <= a -> a + k <= T + 4096 -> (a + k <= T + 2768 \/ T + 3168 <= a) -> disjoint_from W_S a k.
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  intros a k H1 H2 H3. pose proof sl_geo as (G1 & _ & G3 & _ & _ & _ & G7 & G8 & G9 & _ & G11 & G12 & G13 & G14 & G15 & G16 & G17
                                              & G18 & G19 & G20 & _).
  pose proof sl_shad as (_ & _ & S3 & S4 & _).
  pose proof sl_apart as (A1 & _ & _ & _ & _ & _ & _ & A8 & A9 & _ & _ & _ & A13 & _ & _ & _ & _ & _ & _ & A20 & _).
  unfold W_S. cbn [disjoint_from]. unfold apart, SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, INST, g_instance in *.
  split; [clear - A1 H1 H2; destruct A1; lia|]. split; [clear - A20 S3 S4 H1 H2; destruct A20; lia|]. split; [exact H3|].
  pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X23).
  unfold SEGTOP_A in X23.
  split; [clear - X23 H1 H2; destruct X23; lia|]. split; [clear - X23 H1 H2; destruct X23; lia|].
  split; [clear - A8 H1 H2; destruct A8; lia|]. split; [clear - A9 H1 H2; destruct A9; lia|]. split; [clear - A13 H1 H2; destruct A13; lia|].
  split; [lia | exact I].
Qed.

Lemma sw_TCX : forall a k, TCX <= a -> a + k <= TCX + 0x10000 -> disjoint_from W_S a k.
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  intros a k H1 H2. pose proof sl_geo as (G1 & _ & G3 & _ & _ & _ & G7 & G8 & G9 & _ & G11 & G12 & G13 & G14 & G15 & G16 & G17
                                           & G18 & G19 & G20 & _).
  pose proof sl_shad as (_ & _ & S3 & S4 & _).
  pose proof sl_apart as (_ & A2 & _ & _ & _ & _ & A7 & _ & _ & A10 & A11 & _ & _ & A14 & _ & _ & _ & _ & _ & _ & A21 & _).
  unfold W_S. cbn [disjoint_from]. unfold apart, SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, INST, g_instance in *.
  split; [clear - A2 H1 H2; destruct A2; lia|]. split; [clear - A21 S3 S4 H1 H2; destruct A21; lia|].
  split; [clear - A7 H1 H2; destruct A7; lia|]. split; [lia|]. split; [lia|].
  split; [clear - A10 H1 H2; destruct A10; lia|]. split; [clear - A11 H1 H2; destruct A11; lia|].
  split; [clear - A14 H1 H2; destruct A14; lia|].
  split; [lia | exact I].
Qed.

Ltac sw_lit X MU WM := apply (rw_cells_transport ctasegs _ _ _ _ _ X MU WM); cbn [cells_size csize Nat.add];
  apply sw_img; unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, g_got_common_flags, g_can_poison,
    g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset, i_spacebeg, i_sec_page, INST, g_instance, SEGTOP_A; lia.

(* [comment removed for export] *)
Lemma sl_static : forall (m : mem), munch W_T m2 m -> wmono ctasegs m2 m ->
  thread_cells TCX T m /\ m2s_cells m /\ ps_cells m /\ setshadow_cells m
  /\ rw_cells ctasegs m g_GOT_asan_flags [C8 (Z_to_bv 64 g_asan_flags)] /\ rw_cells ctasegs m (g_asan_flags + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells ctasegs m (g_asan_flags + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells ctasegs m (g_asan_flags + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctasegs m (tpA + 32) [C4 (Z_to_bv 64 0)] /\ rw_cells ctasegs m 0x5a9eb0 [C8 (Z_to_bv 64 32)]
  /\ rw_cells ctasegs m g_MFHooks [C8 (Z_to_bv 64 0)] /\ rw_cells ctasegs m g_can_poison_memory [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctasegs m (TCX + 8) [C4 (Z_to_bv 64 0)] /\ rw_cells ctasegs m T [C8 (Z_to_bv 64 TCX)]
  /\ rw_cells ctasegs m i_spacebeg [C8 (Z_to_bv 64 SB)] /\ sec_page m.
Proof using Hn HA HG LOW LOR SPT MU1 WM1. clear - Hn HA HG LOW LOR SPT MU1 WM1.
  intros m MU0 WM0. pose proof (sl_mS m MU0) as MU. pose proof (wmono_trans ctasegs _ _ _ WM1 WM0) as WM. clear MU0 WM0.
  pose proof (ART_consts Σ mA HA) as ((SBC0 & _) & _ & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _
    & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
       & X25 & X26 & X27 & X28 & X29 & X30 & X31 & _ & X33 & _)).
  pose proof (ART_sec Σ mA HA) as (_ & _ & _ & PG & _).
  pose proof sl_geo as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G11 & G12 & G13 & G14 & _).
  assert (SBC : rw_cells ctasegs mA i_spacebeg [C8 (Z_to_bv 64 SB)]) by exact (rw_cells_app_l mA _ [C8 (Z_to_bv 64 SB)] _ SBC0).
  assert (M' : m2s_cells m) by (split; [sw_lit M1 MU WM | split; [sw_lit M2 MU WM | sw_lit M3 MU WM]]).
  assert (SS' : setshadow_cells m) by (split; [sw_lit S1 MU WM | sw_lit S2 MU WM]).
  split.
  { split; [split; [sw_lit T1 MU WM | split; [sw_lit T2 MU WM | split; [sw_lit T3 MU WM | sw_lit T4 MU WM]]]|].
    apply (rw_cells_transport ctasegs _ _ _ _ _ T5 MU WM). cbn [cells_size csize Nat.add]. apply sw_TCX; lia. }
  split; [exact M'|]. split; [split; [sw_lit P1 MU WM | split; [exact M' | split; [exact SS' | split; [sw_lit P3 MU WM | sw_lit P4 MU WM]]]]|].
  split; [exact SS'|].
  split; [sw_lit X23 MU WM|]. split; [sw_lit X24 MU WM|]. split; [sw_lit X25 MU WM|]. split; [sw_lit X26 MU WM|].
  split; [unfold tpA; sw_lit X27 MU WM|]. split; [sw_lit X28 MU WM|]. split; [unfold g_MFHooks; sw_lit X29 MU WM|].
  split; [unfold g_can_poison_memory; sw_lit X30 MU WM|].
  split.
  { apply (rw_cells_transport ctasegs _ _ _ _ _ X31 MU WM). cbn [cells_size csize Nat.add]. apply sw_TCX; lia. }
  split; [apply (rw_cells_transport ctasegs _ _ _ _ _ X33 MU WM); cbn [cells_size csize Nat.add]; apply sw_T; lia|].
  split; [sw_lit SBC MU WM|]. unfold sec_page in *. sw_lit PG MU WM.
Qed.

(* [comment removed for export] *)
Lemma sl_p3stats : forall (m : mem), wmono ctasegs m2 m -> p3_stats m T.
Proof using HA WM1. clear - HA WM1.
  intros m WM0. pose proof (wmono_trans ctasegs _ _ _ WM1 WM0) as WM. clear WM0.
  pose proof (ART_consts Σ mA HA) as (_ & _ & _ & _ & _ & _ & _ & ICR).
  destruct ICR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & St & _).
  pose proof (stk_wmono mA m _ _ St WM) as St'.
  assert (W8 : forall a, T + 2768 <= a -> a + 8 <= T + 3168 -> exists w, rw_cells ctasegs m a [C8 w])
    by (intros a H1 H2; exact (rw_C8_of_stk m _ _ a St' H1 H2)).
  destruct (W8 (T + 2800) ltac:(lia) ltac:(lia)) as (x0 & X0). destruct (W8 (T + 2808) ltac:(lia) ltac:(lia)) as (x1 & X1).
  destruct (W8 (T + 2816) ltac:(lia) ltac:(lia)) as (x2 & X2). destruct (W8 (T + 2904) ltac:(lia) ltac:(lia)) as (x13 & X13).
  split.
  { exists x0, x1, x2. apply (proj2 (sec_rw_app2 m (T + 2800) [C8 x0] [C8 x1; C8 x2])). split; [exact X0|]. cs_size.
    replace (T + 2800 + Z.of_nat 8) with (T + 2808) by lia.
    apply (proj2 (sec_rw_app2 m (T + 2808) [C8 x1] [C8 x2])). split; [exact X1|]. cs_size.
    replace (T + 2808 + Z.of_nat 8) with (T + 2816) by lia. exact X2. }
  split; [exists x13; exact X13|].
  destruct (stk_split ctasegs m (T + 2768) (T + 2912) (T + 3168) St' ltac:(lia)) as [_ X].
  destruct (stk_CB m (T + 2912) 256 ltac:(replace (T + 2912 + 256) with (T + 3168) by lia; exact X) ltac:(lia)) as (bs & Hb).
  exists (ma_dec64 32 bs). split; [apply ma_rw_cells_u64arr; exact Hb | apply ma_dec64_length].
Qed.

(* [comment removed for export] *)
Lemma sl_chunk_stk : forall (m : mem), wmono ctasegs m2 m -> stk ctasegs m P (P + msz).
Proof using SKM. clear - SKM. intros m WM. exact (stk_wmono m2 m _ _ SKM WM). Qed.
Lemma sl_shadow_stk : forall (m : mem), wmono ctasegs m2 m -> stk ctasegs m (shad P) (shad (P + msz)).
Proof using SST. clear - SST. intros m WM. exact (stk_wmono m2 m _ _ SST WM). Qed.

(* [comment removed for export] *)
Lemma sl_dep : depot_ok D DNB SSB (l_ACEIL L) /\ dep_inv D /\ depot_ok (fst (depot_put D tr)) DNB SSB (l_ACEIL L)
  /\ d_n D + 2 < 2 ^ 16 /\ d_tot D + Z.of_nat (length tr) + 1 < 2 ^ 20.
Proof using HA Htrl. clear - HA Htrl.
  pose proof (ART_wf Σ mA HA) as (_ & _ & _ & _ & _ & _ & _ & OK & _ & _ & DI & _).
  pose proof (dep_inv_bounds D DI) as (B1 & B2).
  split; [exact OK|]. split; [exact DI|]. split; [apply depot_ok_put_ok; [exact OK | lia | lia]|]. split; lia.
Qed.

Lemma sl_dep_m2 : depot_rep D BK DNB SSB m2.
Proof using Hn HA HG LOW LOR SPT MU1 WM1 Htrl. clear - Hn HA HG LOW LOR SPT MU1 WM1 Htrl.
  pose proof sl_dep as (OK & _). pose proof sl_geo as (G1 & _ & G3 & _ & _ & _ & G7 & G8 & G9 & _ & G11 & G12 & G13 & G14 & G15 & G16 & G17
                                                        & G18 & G19 & G20 & _).
  pose proof sl_shad as (_ & _ & S3 & S4 & _).
  assert (X : Forall (fun p => kinds (fst p) (snd p)) (W_1 Σ B n P)).
  { unfold W_1, W_1s, INST, g_instance. repeat (apply Forall_cons; [kinds_tac|]). apply Forall_nil. }
  pose proof (sl_dep_avoid _ X) as Y.
  exact (depot_rep_frame _ _ _ _ _ _ mA m2 (ART_dep Σ mA HA) OK MU1 WM1 (proj1 Y) (proj1 (proj2 Y)) (proj1 (proj2 (proj2 Y)))
           (proj1 (proj2 (proj2 (proj2 Y)))) (proj1 (proj2 (proj2 (proj2 (proj2 Y))))) (proj2 (proj2 (proj2 (proj2 (proj2 Y)))))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac piece k Hx := let Hy := fresh "Hy" in intros Hy;
  eapply (not_outside W_T _ _ _ (nth_error_In W_T k eq_refl)); [|exact Hx]; cbn [fst snd]; lia.

Lemma sl_munch_into : forall W (m3 m4 : mem), munch W_T m2 m3 -> munch W m3 m4 -> sub_fp W W_T -> munch W_T m2 m4.
Proof. intros W m3 m4 MU MU' Hs. exact (munch_into _ _ m2 m3 m4 MU MU' Hs). Qed.

(* [comment removed for export] *)
Lemma sl_p3b : forall (m6 : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0v s6v s9v s3v : word)
    (h0 : list byte) (b1 : Z) (ctx : word),
  munch W_T m2 m6 -> wmono ctasegs m2 m6 -> mem_inv ctasegs m6 -> stk ctasegs m6 lo (B + -144) ->
  af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m6 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells ctasegs m6 (AB + 2048 + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at ctasegs m6 (shad (AB + 2048)) (ushadow n) -> bytes_at ctasegs m6 (shad AB) (farun (2048 / 8)) ->
  bytes_at ctasegs m6 (shad (AB + 2048 + ru8 n)) (farun ((S - 2048 - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m6 ->
  evt ctasegs sl_post (MS (mkR ra0 (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) s3v (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) s6v
                             (Z_to_bv 64 B) (Z_to_bv 64 0) s9v (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x19c3c8) fc None m6 (seg_rom ctasegs)).
Proof using Hn HA HG LOW LOR SPT SPA MU1 WM1 SKM SST Htrl. clear - Hn HA HG LOW LOR SPT SPA MU1 WM1 SKM SST Htrl.
  intros m6 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0v s6v s9v s3v h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD US RZ1 RZ2 DR.
  pose proof sl_sizes as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13).
  pose proof sl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  pose proof sl_shad as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
  apply hidep_of in H10. apply hidep_of in H11.
  pose proof sl_room as (SR & SR2).
  pose proof (sl_chunk_stk m6 WM) as CH.
  assert (CH2 : stk ctasegs m6 (AB + 2048) (AB + 2048 + Z.min n 4096)).
  { pose proof (proj2 (stk_split ctasegs m6 P (AB + 2048) (P + msz) CH ltac:(lia))) as X.
    exact (proj1 (stk_split ctasegs m6 (AB + 2048) (AB + 2048 + Z.min n 4096) (P + msz) X ltac:(lia))). }
  destruct (stk_CB m6 (AB + 2048) (Z.min n 4096) CH2 ltac:(lia)) as (uj & UJ).
  destruct (stk_CB m6 AB 16 ltac:(apply (proj1 (stk_split ctasegs m6 AB (AB + 16) (P + msz)
                                    (proj2 (stk_split ctasegs m6 P AB (P + msz) CH ltac:(lia))) ltac:(lia)))) ltac:(lia)) as (lj & LJ).
  destruct (sl_static m6 MU WM) as (_ & _ & _ & SS & GAF & F44 & F52 & _ & TP16 & G9a & MFH & _).
  destruct AF as (AF & J0).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by lia.
  eapply evt_mono.
  { apply (allocate_p3b_specL (Z_to_bv 64 (B + -144)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s6v s9v s3v
             (Z_to_bv 64 0x19bcec) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m6 n AB B T lo b1 h0 uj lj j0 ctx);
      rewrite ?(unsigned_lit (B + -144)) by exact RS; rewrite ?Z1; try assumption; try (intros _; exact LJ);
      unfold kHighShadowEnd, kHighMemEnd, SEGTOP_A in *; lia. }
  intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m7 & -> & MU7 & WM7 & MI7 & HD7 & UJ7 & LCH7 & ST7).
  rewrite (unsigned_lit (B + -144)) in MU7, ST7 by exact RS. rewrite sp_off by exact RS. rewrite Z1 in *.
  replace (B + -144 + 128) with (B + -16) in * by lia.
  assert (D7 : forall a k, 0 <= k -> (a + k <= AB \/ P + msz <= a) -> (a + k <= B + -176 \/ B + -16 <= a) ->
               disjoint_from [(AB, AB + 16); (AB + 2048 + -16, AB + 2048 + Z.min n 4096); (B + -144 - 32, B + -16)] a k).
  { intros a k Hk X1 X2. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (DSH : forall a k, 0 <= k -> shad P <= a -> a + k <= shad (P + msz) ->
               disjoint_from [(AB, AB + 16); (AB + 2048 + -16, AB + 2048 + Z.min n 4096); (B + -144 - 32, B + -16)] a k).
  { intros a k Hk X1 X2. apply D7; [exact Hk | destruct (sl_map_vs_shad P msz ltac:(lia) ltac:(lia) a (a + k) X1 X2) as [Xd|Xd]; lia | lia]. }
  exists m7. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split.
  { apply (sl_munch_into _ m6 m7 MU MU7). intros x Hx. cbn [outside]. split; [piece 0%nat Hx|]. split; [piece 0%nat Hx|].
    split; [piece 6%nat Hx | exact I]. }
  split; [exact (wmono_trans ctasegs _ _ _ WM WM7)|]. split; [exact MI7|]. split; [exact ST7|].
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof sl_dep as (_ & _ & OK' & _).
  split; [exists (Z_to_bv 8 (Z.land b1 243)), ctx; split; [exact (land243_mod4 b1 Hb1 Hb4) | replace (AB + 2032) with (AB + 2048 + -16) by lia; exact HD7]|].
  split; [unfold lch; replace (AB + 2032) with (AB + 2048 + -16) by lia; exact (LCH7 ltac:(lia))|].
  split; [apply (bytes_at_transport ctasegs _ m6 m7 _ _ US MU7); apply DSH; [lia | rewrite H5; lia | rewrite H5, Z10; lia]|].
  split; [apply (bytes_at_transport ctasegs _ m6 m7 _ _ RZ1 MU7); apply DSH; [lia | lia | rewrite FL by lia; change (2048 / 8) with 256; lia]|].
  split; [apply (bytes_at_transport ctasegs _ m6 m7 _ _ RZ2 MU7); apply DSH; [lia | rewrite H6; lia | rewrite H6, FL by lia; lia]|].
  dep_frame DR OK' MU7 WM7.
Qed.

(* [comment removed for export] *)
Lemma sl_p3a : forall (m5 : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0v s9v : word)
    (h0 : list byte) (b1 : Z) (ctx : word),
  munch W_T m2 m5 -> wmono ctasegs m2 m5 -> mem_inv ctasegs m5 -> stk ctasegs m5 lo (B + -144) ->
  af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m5 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells ctasegs m5 (AB + 2048 + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at ctasegs m5 (shad (AB + 2048)) (zrun (size_rd n / 8)) -> bytes_at ctasegs m5 (shad AB) (farun (2048 / 8)) ->
  bytes_at ctasegs m5 (shad (AB + 2048 + ru8 n)) (farun ((S - 2048 - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m5 ->
  evt ctasegs sl_post (MS (mkR ra0 (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                             (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 B) (Z_to_bv 64 0) s9v (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x19c1d4) fc None m5 (seg_rom ctasegs)).
Proof using Hn HA HG LOW LOR SPT SPA MU1 WM1 SKM SST Htrl. clear - Hn HA HG LOW LOR SPT SPA MU1 WM1 SKM SST Htrl.
  intros m5 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0v s9v h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD ZR RZ1 RZ2 DR.
  pose proof sl_sizes as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13).
  pose proof sl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  pose proof sl_shad as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
  apply hidep_of in H10. apply hidep_of in H11.
  pose proof (sl_shadow_stk m5 WM) as SST5. pose proof sl_room as (SR & SR2).
  destruct (sl_static m5 MU WM) as (TC & M2S & _ & _ & GAF & _ & _ & F85 & _ & _ & _ & CP & _ & _).
  assert (S8 : 0 <= size_rd n / 8) by (apply Z.div_pos; lia). assert (U8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
  assert (PBx : exists pb : byte, n mod 8 <> 0 -> rw_cells ctasegs m5 (shad (AB + 2048 + size_rd n)) [C1 pb]).
  { destruct (Z.eq_dec (n mod 8) 0) as [Hm0|Hm0]; [exists (Z_to_bv 8 0); intros X; contradiction|].
    pose proof (H10 Hm0) as X10.
    destruct (rw_C1_of m5 (shad (AB + 2048 + size_rd n))
                ltac:(rewrite H7; apply (proj1 (stk_split ctasegs m5 _ (shad AB + 256 + size_rd n / 8 + 1) _
                        (proj2 (stk_split ctasegs m5 (shad P) (shad AB + 256 + size_rd n / 8) _ SST5 ltac:(lia))) ltac:(lia)))))
      as (pb & PB).
    exists pb. intros _. exact PB. }
  destruct PBx as (pb & PB).
  destruct AF as (AF & J0).
  pose proof sl_apart as (_ & _ & _ & _ & _ & _ & A7 & _).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by lia.
  assert (Hplace : kHighShadowEnd < AB \/ AB + needed2 n <= kLowMemEnd + 1).
  { pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _).
    clear - X Z3 G3 SR Hn.
    unfold kHighShadowEnd, kLowMemEnd, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. destruct X; [right | left]; lia. }
  pose proof (sl_p3stats m5 WM) as P3S. pose proof sl_objs as (O1 & O2 & O3 & O4).
  eapply evt_cut.
  { destruct Hplace as [HH|HL].
    - apply (allocate_p3a_spec (Z_to_bv 64 (B + -144)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s9v
             (Z_to_bv 64 0x19bcec) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m5 n AB B TCX T lo pb);
        rewrite ?(unsigned_lit (B + -144)) by exact RS; rewrite ?Z1; try assumption; try exact PB;
        try exact O1; try exact O2; try exact O3; try exact O4;
        clear_disj; unfold kHighShadowEnd, kHighMemEnd, SEGTOP_A, K_HIGH_SHADOW_hi, SHB in *; lia.
    - apply (allocate_p3a_specL (Z_to_bv 64 (B + -144)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s9v
             (Z_to_bv 64 0x19bcec) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m5 n AB B TCX T lo pb);
        rewrite ?(unsigned_lit (B + -144)) by exact RS; rewrite ?Z1; try assumption; try exact PB;
        try exact O1; try exact O2; try exact O3; try exact O4;
        clear_disj; unfold kHighShadowEnd, kHighMemEnd, SEGTOP_A, K_HIGH_SHADOW_hi, SHB in *; lia. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s6' & m6 & -> & MU6 & WM6 & MI6 & SC6 & PB6 & ST6).
  rewrite (unsigned_lit (B + -144)) in MU6, ST6 by exact RS. rewrite Z1 in MU6, PB6. rewrite H7 in MU6, PB6.
  set (PW := if n mod 8 =? 0 then 0 else 1) in MU6.
  assert (HPW : 0 <= PW <= 1 /\ (n mod 8 = 0 -> PW = 0) /\ (n mod 8 <> 0 -> PW = 1)).
  { unfold PW. destruct (Z.eqb_spec (n mod 8) 0); lia. }
  clearbody PW. destruct HPW as (PW1 & PW2 & PW3).
  assert (HPWb : size_rd n / 8 + PW <= ru8 n / 8).
  { destruct (Z.eq_dec (n mod 8) 0) as [Hm|Hm]; [rewrite (PW2 Hm); lia | rewrite (PW3 Hm), <- (H10 Hm); lia]. }
  apply hidep_of in PW2. apply hidep_of in PW3.
  assert (D6 : forall a k, 0 <= k -> (a + k <= shad AB + 256 + size_rd n / 8 \/ shad AB + 256 + size_rd n / 8 + PW <= a) ->
               (a + k <= T + 2800 \/ T + 3168 <= a) -> (a + k <= B + -144 - 32 \/ B + -144 <= a) ->
               disjoint_from [(shad AB + 256 + size_rd n / 8, shad AB + 256 + size_rd n / 8 + PW); (T + 2800, T + 2824);
                              (T + 2904, T + 2912 + 256); (B + -144 - 32, B + -144)] a k).
  { intros a k Hk X1 X2 X3. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (USH : bytes_at ctasegs m6 (shad (AB + 2048)) (ushadow n)).
  { pose proof (bytes_at_transport ctasegs _ m5 m6 _ _ ZR MU6) as ZR6.
    assert (Lz : Z.of_nat (length (zrun (size_rd n / 8))) = size_rd n / 8) by (unfold zrun; rewrite repeat_length; lia).
    rewrite Lz in ZR6. specialize (ZR6 ltac:(rewrite H5; apply D6; [lia | lia
      | destruct (sl_shad_vs_T (shad AB + 256) (shad AB + 256 + size_rd n / 8) ltac:(lia) ltac:(lia) (T + 2800) 368 ltac:(lia) ltac:(lia)) as [Xd|Xd]; lia
      | lia])).
    assert (E8' : size_rd n / 8 = n / 8) by (unfold size_rd; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    unfold ushadow. unfold zrun in ZR6. rewrite E8' in ZR6. destruct (Z.eqb_spec (n mod 8) 0) as [Hm|Hm].
    - rewrite app_nil_r. exact ZR6.
    - apply bytes_at_app. split; [exact ZR6|]. rewrite repeat_length, Z2Nat.id by (apply Z.div_pos; lia). rewrite H5.
      destruct (PB6 Hm) as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. rewrite <- E8'. exact Hb. }
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  assert (DSH : forall a k, 0 <= k -> shad P <= a -> a + k <= shad (P + msz) ->
               (a + k <= shad AB + 256 + size_rd n / 8 \/ shad AB + 256 + size_rd n / 8 + PW <= a) ->
               disjoint_from [(shad AB + 256 + size_rd n / 8, shad AB + 256 + size_rd n / 8 + PW); (T + 2800, T + 2824);
                              (T + 2904, T + 2912 + 256); (B + -144 - 32, B + -144)] a k).
  { intros a k Hk X1 X2 X3. apply D6; [lia | exact X3 | destruct (sl_shad_vs_T a (a + k) X1 X2 (T + 2800) 368 ltac:(lia) ltac:(lia)) as [Xd|Xd]; lia
                                      | unfold SHB in *; lia]. }
  apply (sl_p3b m6 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ra' s0v s6' s9v (Z_to_bv 64 (needed2 n)) h0 b1 ctx).
  - apply (sl_munch_into _ m5 m6 MU MU6). intros x Hx. cbn [outside]. split; [piece 1%nat Hx|]. split; [piece 2%nat Hx|].
    split; [piece 2%nat Hx|]. split; [piece 6%nat Hx | exact I].
  - exact (wmono_trans ctasegs _ _ _ WM WM6).
  - exact MI6.
  - exact ST6.
  - apply (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m5 m6 _ (conj AF J0) MU6 WM6).
    apply D6; unfold SEGTOP_A, SHB in *; lia.
  - exact Hb1.
  - exact Hb4.
  - apply (rw_cells_transport ctasegs _ m5 m6 _ _ HD MU6 WM6). cbn [cells_size csize Nat.add]. apply D6; [lia
      | destruct (sl_map_vs_shad (AB + 2048 + -16) (Z.of_nat 16) ltac:(lia) ltac:(lia) (shad AB + 256 + size_rd n / 8)
                      (shad AB + 256 + size_rd n / 8 + PW) ltac:(lia) ltac:(lia)) as [Xd|Xd]; lia
      | destruct (sl_map_vs_T (AB + 2048 + -16) (Z.of_nat 16) ltac:(lia) ltac:(lia) (T + 2800) 368 ltac:(lia) ltac:(lia)) as [Xd|Xd]; lia
      | lia].
  - exact USH.
  - apply (bytes_at_transport ctasegs _ m5 m6 _ _ RZ1 MU6). rewrite FL by lia. change (2048 / 8) with 256. apply DSH; lia.
  - apply (bytes_at_transport ctasegs _ m5 m6 _ _ RZ2 MU6). rewrite FL by lia. rewrite H6. apply DSH; [lia | lia | lia |].
    right. destruct (Z.eqb_spec (n mod 8) 0) as [Hm|Hm]; [rewrite (PW2 Hm), (H11 Hm); lia | rewrite (PW3 Hm), <- (H10 Hm); lia].
  - pose proof sl_dep as (_ & _ & OK' & _).
    dep_frame DR OK' MU6 WM6.
Qed.

(* [comment removed for export] *)
Definition ps_st (m4 : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
  MS (mkR (Z_to_bv 64 0x19c1d4) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (sec_ru n)) (Z_to_bv 64 n)
          (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 AB)
          (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
          (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n + 7))
          (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
     F (Z_to_bv 64 ps_entry) fc None m4 (seg_rom ctasegs).

(* [comment removed for export] *)
Definition ps_facts (m4 : mem) (h0 : list byte) (b1 : Z) (ctx : word) : Prop :=
  munch W_T m2 m4 /\ wmono ctasegs m2 m4 /\ mem_inv ctasegs m4 /\ stk ctasegs m4 lo (B + -144)
  /\ af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m4 j0 /\ 0 <= b1 < 256 /\ b1 mod 4 = 1
  /\ rw_cells ctasegs m4 (AB + 2048 + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx]
  /\ bytes_at ctasegs m4 (shad AB) (farun (2048 / 8))
  /\ bytes_at ctasegs m4 (shad (AB + 2048 + ru8 n)) (farun ((S - 2048 - ru8 n) / 8))
  /\ depot_rep (fst (depot_put D tr)) BK DNB SSB m4.

(* [comment removed for export] *)
Definition ps_k (Q : machine_state -> Prop) : Prop :=
  forall (m4 : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (h0 : list byte) (b1 : Z) (ctx : word),
    ps_facts m4 h0 b1 ctx -> evt ctasegs Q (ps_st m4 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6).

(* [comment removed for export] *)
Lemma sl_user_shadow : forall (m : mem), wmono ctasegs m2 m -> exists shj, rw_cells ctasegs m (shad (AB + rz_size n)) [CB (Z.to_nat (size_rd n / 8)) shj].
Proof using Hn HA HG LOW LOR SPT SST. clear - Hn HA HG LOW LOR SPT SST.
  intros m WM. pose proof sl_sizes as (Z1 & _). pose proof sl_shad as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
  pose proof (sl_shadow_stk m WM) as SS. rewrite Z1, H5.
  assert (S8 : 0 <= size_rd n / 8) by (apply Z.div_pos; pose proof sl_sizes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Z12 & _); lia).
  assert (0 <= ru8 n / 8) by lia.
  apply (stk_CB m (shad AB + 256) (size_rd n / 8)); [|exact S8].
  apply (proj1 (stk_split ctasegs m _ (shad AB + 256 + size_rd n / 8) _ (proj2 (stk_split ctasegs m (shad P) (shad AB + 256) _ SS ltac:(lia)))
           ltac:(lia))).
Qed.

Lemma sl_ps_args : ps_args_ok (AB + rz_size n) (size_rd n).
Proof using Hn HA HG LOW LOR SPT. clear - Hn HA HG LOW LOR SPT.
  pose proof sl_sizes as (Z1 & _ & Z3 & _ & _ & _ & _ & Z8 & Z9 & _ & Z11 & Z12 & Z13). pose proof sl_shad as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H16).
  pose proof sl_room as (SR & _). pose proof sl_geo as (G1 & G2 & G3 & _ & _ & _ & G7 & G8 & _).
  pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _).
  rewrite Z1. unfold ps_args_ok. split; [split; [exact H16|]; split; [exact Z11 | lia]|].
  clear - X G1 G3 G8 SR Z8 Z12. unfold kLowMemEnd, kHighShadowEnd, kHighMemEnd, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *.
  destruct X; [left | right]; lia.
Qed.

(* [comment removed for export] *)
Lemma sl_psS : ps_k sl_post.
Proof using Hn HA HG LOW LOR SPT SPA Htrl MU1 WM1 SKM SST. clear - Hn HA HG LOW LOR SPT SPA Htrl MU1 WM1 SKM SST.
  intros m4 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h0 b1 ctx (MU & WM & MI & ST & AF & Hb1 & Hb4 & HD & RZ1 & RZ2 & DR).
  pose proof sl_sizes as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13).
  assert (Hsm : size_rd n / 8 < 0xffffffffffffffff) by (apply Z.div_lt_upper_bound; lia).
  pose proof sl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  pose proof sl_shad as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
  apply hidep_of in H10. apply hidep_of in H11.
  destruct (sl_static m4 MU WM) as (_ & _ & PSC & _).
  destruct (sl_user_shadow m4 WM) as (shj & SHJ).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by lia.
  unfold ps_st.
  eapply evt_cut.
  { apply (poison_small_spec (Z_to_bv 64 0x19c1d4) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (sec_ru n)) (Z_to_bv 64 n)
             a3 a4 a5 a6 a7 (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
             (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n + 7)) (Z_to_bv 64 T) (Z_to_bv 64 1)
             t3 t4 t5 t6 F fc m4 (AB + rz_size n) (size_rd n) 0 lo shj sl_ps_args ltac:(lia) (or_intror Hsm) SHJ PSC
             ltac:(rewrite (unsigned_lit (B + -144)) by exact RS; exact ST));
      rewrite ?(unsigned_lit (B + -144)) by exact RS; [lia | unfold kHighShadowEnd in *; lia | exact MI]. }
  intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & -> & MU5 & WM5 & MI5 & ZR5 & ST5).
  rewrite (unsigned_lit (B + -144)) in MU5, ST5 by exact RS. rewrite (ret_pc_even 0x19c1d4) by (lia || reflexivity).
  rewrite Z1, H5 in MU5, ZR5.
  assert (D5 : forall a k, 0 <= k -> (a + k <= shad AB + 256 \/ shad AB + 256 + size_rd n / 8 <= a) ->
               (a + k <= B + -144 - 64 \/ B + -144 <= a) ->
               disjoint_from [(shad AB + 256, shad AB + 256 + size_rd n / 8); (B + -144 - 64, B + -144)] a k).
  { intros a k Hk X1 X2. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  assert (DFAR : forall a k, 0 <= k -> (a + k <= shad AB + 256 \/ shad AB + 256 + size_rd n / 8 <= a) -> a + k <= l_ACEIL L ->
               disjoint_from [(shad AB + 256, shad AB + 256 + size_rd n / 8); (B + -144 - 64, B + -144)] a k).
  { intros a k Hk X1 X2. apply D5; [lia | lia | left; lia]. }
  assert (S8 : 0 <= size_rd n / 8) by (apply Z.div_pos; lia).
  apply (sl_p3a m5 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (Z_to_bv 64 0x19c1d4) (Z_to_bv 64 (sec_ru n))
           (Z_to_bv 64 (AB + rz_size n + n + 7)) h0 b1 ctx).
  - apply (sl_munch_into _ m4 m5 MU MU5). intros x Hx. cbn [outside]. split; [piece 1%nat Hx|]. split; [piece 6%nat Hx | exact I].
  - exact (wmono_trans ctasegs _ _ _ WM WM5).
  - exact MI5.
  - exact ST5.
  - apply (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m4 m5 _ AF MU5 WM5).
    apply D5; [lia | unfold SHB in *; lia | lia].
  - exact Hb1.
  - exact Hb4.
  - apply (rw_cells_transport ctasegs _ m4 m5 _ _ HD MU5 WM5). cbn [cells_size csize Nat.add]. apply DFAR; [lia
      | destruct (sl_map_vs_shad (AB + 2048 + -16) (Z.of_nat 16) ltac:(lia) ltac:(lia) (shad AB + 256) (shad AB + 256 + size_rd n / 8)
                      ltac:(lia) ltac:(lia)) as [Xd|Xd]; lia | lia].
  - rewrite H5. destruct ZR5 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - apply (bytes_at_transport ctasegs _ m4 m5 _ _ RZ1 MU5). rewrite FL by lia. change (2048 / 8) with 256. apply DFAR; lia.
  - apply (bytes_at_transport ctasegs _ m4 m5 _ _ RZ2 MU5). rewrite FL by lia. rewrite H6. apply DFAR; lia.
  - pose proof sl_dep as (_ & _ & OK' & _).
    dep_frame DR OK' MU5 WM5.
Qed.

(* [comment removed for export] *)
Lemma sl_p2S : forall Q, ps_k Q -> forall (m3 : mem) (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (h0 : list byte) (b1 : Z) (ctx : word),
  munch W_T m2 m3 -> wmono ctasegs m2 m3 -> mem_inv ctasegs m3 -> stk ctasegs m3 lo (B + -144) ->
  af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m3 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells ctasegs m3 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m3 ->
  evt ctasegs Q (MS (mkR ra' (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n)
                     a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n))
                     (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n))
                     (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x19c0d8) fc None m3 (seg_rom ctasegs)).
Proof using Hn HA HG LOW LOR SPT SPA Htrl MU1 WM1 SKM SST HDR. clear - Hn HA HG LOW LOR SPT SPA Htrl MU1 WM1 SKM SST HDR.
  intros Q HK m3 ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD DR.
  pose proof sl_sizes as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13).
  pose proof sl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  pose proof sl_shad as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
  apply hidep_of in H10. apply hidep_of in H11.
  pose proof sl_room as (SR & SR2).
  destruct (sl_static m3 MU WM) as (_ & _ & PSC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SBC & PGC).
  rewrite Z2. cbn [Z.b2z].
  (* [comment removed for export] *)
  assert (HSZ : rw_cells ctasegs m3 (AB - 4096 + 16) [C8 (Z_to_bv 64 (needed2 n))]).
  { unfold shdr in HDR. pose proof (proj2 (proj1 (sec_rw_app2 m2 P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 msz)]
                                      [C8 (Z_to_bv 64 (needed2 n)); C8 (Z_to_bv 64 (Z.of_nat (length (sec Σ))))]) HDR)) as X.
    cs_size. pose proof (rw_cells_app_l m2 _ [C8 (Z_to_bv 64 (needed2 n))] _ X) as X'.
    replace (AB - 4096 + 16) with (P + Z.of_nat 16) by lia.
    apply (rw_cells_transport ctasegs _ m2 m3 _ _ X' MU WM). cs_size. exact (sl_map_avoid_WT (P + Z.of_nat 16) (Z.of_nat 8) ltac:(lia) ltac:(lia)). }
  (* [comment removed for export] *)
  pose proof (sl_shadow_stk m3 WM) as SS3.
  assert (TB : sec_tb n AB = AB + 2048 + ru8 n).
  { unfold sec_tb. rewrite Z1. unfold ru8. replace (AB + 2048 + n + 7) with ((AB + 2048) + (n + 7)) by ring.
    apply Z.mod_divide in H16; [|lia]. destruct H16 as [q Eq]. rewrite Eq.
    replace (q * 8 + (n + 7)) with ((n + 7) + q * 8) by ring. rewrite Z.div_add by lia. lia. }
  assert (RU : AB + sec_ru n - sec_tb n AB = S - 2048 - ru8 n) by (rewrite TB, Z7; lia).
  destruct (stk_CB m3 (shad AB) (rz_size n / 8) ltac:(rewrite Z1; change (2048 / 8) with 256;
              exact (proj1 (stk_split ctasegs m3 _ (shad AB + 256) _ (proj2 (stk_split ctasegs m3 (shad P) (shad AB) _ SS3 ltac:(lia))) ltac:(lia))))
              ltac:(rewrite Z1; lia)) as (sj1 & SJ1).
  assert (SS3' : stk ctasegs m3 (shad AB + 256 + ru8 n / 8) (shad AB + 256 + ru8 n / 8 + (S / 8 - 256 - ru8 n / 8))).
  { replace (shad AB + 256 + ru8 n / 8 + (S / 8 - 256 - ru8 n / 8)) with (shad (P + msz)) by lia.
    exact (proj2 (stk_split ctasegs m3 (shad P) (shad AB + 256 + ru8 n / 8) (shad (P + msz)) SS3 ltac:(lia))). }
  destruct (stk_CB m3 (shad (sec_tb n AB)) ((AB + sec_ru n - sec_tb n AB) / 8)
              ltac:(rewrite RU, TB, H6, H12; exact SS3') ltac:(rewrite RU; exact H13)) as (sj2 & SJ2).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by lia.
  assert (HSB : AB + sec_ru n <= SB \/ SB + 2 ^ 37 <= AB).
  { pose proof sl_apart as (_ & _ & _ & _ & A5 & _). pose proof (geo_prb Σ mA HA) as (P1 & P2 & P3). rewrite Z7. clear - A5 P1 P2 G3.
    unfold apart in A5. destruct A5; [left | right]; lia. }
  assert (HMAP : (0 <= AB - 4096 /\ AB + sec_ru n <= kLowMemEnd + 1) \/ (kHighShadowEnd < AB - 4096 /\ AB + sec_ru n <= kHighMemEnd + 1)).
  { pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). rewrite Z7. clear - X G1 G3 G8.
    unfold kLowMemEnd, kHighShadowEnd, kHighMemEnd, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *. destruct X; [left | right]; lia. }
  eapply evt_cut.
  { apply (allocate_p2S_spec (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m3 n AB
             B T SB lo (Z_to_bv 64 (needed2 n)) sj1 sj2 ltac:(lia) Z2 ltac:(rewrite Z.add_mod, G2 by lia; reflexivity) HSB HMAP SBC
             ltac:(unfold sec_page, i_sec_page, INST in PGC; exact PGC) HSZ SJ1 SJ2 PSC
             ltac:(rewrite (unsigned_lit (B + -144)) by exact RS; exact ST));
      rewrite ?(unsigned_lit (B + -144)) by exact RS; [lia | unfold kHighShadowEnd in *; lia | lia | exact MI]. }
  intros ms (m4 & HS & MU4 & WM4 & MI4 & (RZ1 & RZ2) & ST4).
  rewrite (unsigned_lit (B + -144)) in MU4, ST4 by exact RS.
  rewrite (proj2 (Z.leb_le 8 n) ltac:(lia)) in HS.
  destruct HS as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
  rewrite RU, TB, Z1 in MU4. rewrite RU, TB in RZ2. rewrite Z1 in RZ1. change (2048 / 8) with 256 in MU4, RZ1.
  assert (D4 : forall a k, 0 <= k -> (a + k <= shad AB \/ shad AB + 256 <= a) ->
               (a + k <= shad (AB + 2048 + ru8 n) \/ shad (AB + 2048 + ru8 n) + (S - 2048 - ru8 n) / 8 <= a) ->
               (a + k <= B + -144 - 64 \/ B + -144 <= a) ->
               disjoint_from [(shad AB, shad AB + 256); (shad (AB + 2048 + ru8 n), shad (AB + 2048 + ru8 n) + (S - 2048 - ru8 n) / 8);
                              (B + -144 - 64, B + -144)] a k).
  { intros a k Hk X1 X2 X3. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (DFAR : forall a k, 0 <= k -> (a + k <= shad P \/ shad (P + msz) <= a) -> a + k <= l_ACEIL L ->
               disjoint_from [(shad AB, shad AB + 256); (shad (AB + 2048 + ru8 n), shad (AB + 2048 + ru8 n) + (S - 2048 - ru8 n) / 8);
                              (B + -144 - 64, B + -144)] a k).
  { intros a k Hk X1 X2.
    pose proof (Z.div_le_lower_bound msz 8 768 ltac:(lia) ltac:(clear - G4; lia)) as Q8.
    pose proof (Z.div_pos (ru8 n) 8 ltac:(clear - Z8 Hn; lia) ltac:(lia)) as Q9.
    apply D4; [exact Hk | destruct X1 as [X|X]; [left|right]; clear - X H1 H2 Q8; lia
                        | destruct X1 as [X|X]; [left|right]; clear - X H1 H6 H12 H15 Q9; lia | left; clear - X2 LOW LOR; lia]. }
  apply (HK m4 t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' h0 b1 ctx).
  split.
  { apply (sl_munch_into _ m3 m4 MU MU4). intros x Hx. cbn [outside]. split; [piece 1%nat Hx|]. split; [piece 1%nat Hx|].
    split; [piece 6%nat Hx | exact I]. }
  split; [exact (wmono_trans ctasegs _ _ _ WM WM4)|]. split; [exact MI4|]. split; [exact ST4|].
  split; [apply (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m3 m4 _ AF MU4 WM4);
          apply D4; unfold SHB in *; lia|].
  split; [exact Hb1|]. split; [exact Hb4|].
  split; [rewrite Z1 in HD; apply (rw_cells_transport ctasegs _ m3 m4 _ _ HD MU4 WM4); cbn [cells_size csize Nat.add];
          apply DFAR; [lia | destruct (sl_map_vs_shad (AB + 2048 + -16) (Z.of_nat 16) ltac:(lia) ltac:(lia) (shad P) (shad (P + msz))
                                       ltac:(lia) ltac:(lia)) as [Xd|Xd]; lia | lia]|].
  split; [destruct RZ1 as [[_ Hb] _]; cbn [cells_bytes cbytes] in Hb; rewrite app_nil_r in Hb; exact Hb|].
  split; [destruct RZ2 as [[_ Hb] _]; cbn [cells_bytes cbytes] in Hb; rewrite app_nil_r in Hb; exact Hb|].
  pose proof sl_dep as (_ & _ & OK' & _).
  dep_frame DR OK' MU4 WM4.
Qed.

(* [comment removed for export] *)
Lemma sl_p2a : forall Q, ps_k Q -> forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (tb : list word),
  mem_inv ctasegs m2 -> stk ctasegs m2 lo (B + -144) ->
  af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m2 j0 -> trc_cells B tr m2 tb ->
  evt ctasegs Q (MS (mkR (Z_to_bv 64 0x19bfbc) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2
                      (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B)
                      (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x19bfbc) fc None m2 (seg_rom ctasegs)).
Proof using Hn HA HG LOW LOR SPT SPA Htr Htrl MU1 WM1 SKM SST HDR. clear - Hn HA HG LOW LOR SPT SPA Htr Htrl MU1 WM1 SKM SST HDR.
  intros Q HK t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tb MI ST AF IC.
  pose proof sl_sizes as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13).
  pose proof sl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  pose proof sl_room as (SR & SR2).
  pose proof sl_dep as (OK & DI & OK' & DN2 & DT).
  pose proof (munch_refl W_T m2) as MU0.
  destruct (sl_static m2 MU0 (wmono_refl ctasegs m2)) as (TC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TX8 & TT0 & _).
  pose proof (sl_chunk_stk m2 (wmono_refl ctasegs m2)) as CH.
  destruct (stk_CB m2 (AB + rz_size n - 16) 16 ltac:(rewrite Z1; apply (proj1 (stk_split ctasegs m2 _ (AB + 2048 - 16 + 16) _
              (proj2 (stk_split ctasegs m2 P (AB + 2048 - 16) _ CH ltac:(lia))) ltac:(lia)))) ltac:(lia)) as (hdr & HD).
  destruct IC as (I6 & I4 & HTB).
  assert (I6' : rw_cells ctasegs m2 B [C8 (Z_to_bv 64 (B + 16)); C8 (Z_to_bv 64 (Z.of_nat (length (map (Z_to_bv 64) tr))))])
    by (rewrite map_length; exact I6).
  assert (I4' : u64arr ctasegs m2 (B + 16) (map (Z_to_bv 64) tr ++ skipn (length tr) tb)) by exact I4.
  assert (RS : 0 <= B + -144 < 2 ^ 64) by lia.
  pose proof (T_MAIN_range tr Htr) as TRR.
  assert (HBK : In (bkt (depot_hash (map bv_unsigned (map (Z_to_bv 64) tr)))) BK).
  { rewrite (map_unsigned_lit tr TRR). unfold DEP_BK. right. apply in_map_iff. exists tr. split; [reflexivity | exact Htr]. }
  pose proof (sl_dep_m2) as DR.
  eapply evt_cut.
  { apply (allocate_p2a_spec (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
             (Z_to_bv 64 0x19bcec) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m2 n AB B TCX T lo hdr D BK DNB SSB
             (map (Z_to_bv 64) tr) (skipn (length tr) tb)); rewrite ?(unsigned_lit (B + -144)) by exact RS.
    - lia.
    - unfold SEGTOP_A in *. lia.
    - apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply (Z.divide_trans 16 4096); [exists 256; reflexivity | apply Z.mod_divide; [lia | exact G2]]
                                                     | exists 256; reflexivity].
    - lia.
    - exact HD.
    - exact (proj1 AF).
    - exact TT0.
    - exact TX8.
    - exact I6'.
    - exact I4'.
    - rewrite app_length, map_length, skipn_length. lia.
    - rewrite map_length. lia.
    - apply (depot_ok_mono _ _ _ _ _ OK). lia.
    - exact DR.
    - rewrite map_length. exact DT.
    - exact HBK.
    - exact DN2.
    - exact ST.
    - lia.
    - lia.
    - lia.
    - pose proof sl_apart as (X & _). unfold apart in X. clear - X SR Z3. destruct X; lia.
    - pose proof sl_apart as (_ & X & _). unfold apart in X. clear - X SR Z3. destruct X; lia.
    - pose proof sl_apart as (_ & _ & X & _). unfold apart in X. clear - X SR Z3. destruct X; lia.
    - pose proof sl_apart as (_ & _ & _ & X & _). unfold apart in X. clear - X SR Z3. destruct X; lia.
    - unfold SEGTOP_A in *. lia.
    - unfold SEGTOP_A in *. lia.
    - pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & X & _). unfold apart in X. clear - X. destruct X; lia.
    - pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & X & _). unfold apart in X. clear - X. destruct X; lia.
    - pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). unfold apart in X. clear - X. destruct X; lia.
    - pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). unfold apart in X. clear - X. destruct X; lia.
    - pose proof sl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X).
      unfold SEGTOP_A in X. exact X.
    - unfold SEGTOP_A in *. lia.
    - exact MI. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & HD3 & DR3 & TB3 & ST3).
  rewrite (unsigned_lit (B + -144)) in MU3, ST3 by exact RS. rewrite (map_unsigned_lit tr TRR) in HD3, DR3.
  pose proof (hb1_props (hdr_b1 hdr) (hdr_b1_range hdr)) as (HB1 & HB4).
  assert (D3 : forall a k, 0 <= k -> (a + k <= AB + rz_size n + -16 \/ AB + rz_size n <= a) ->
               (a + k <= 0x743f08 \/ 0xb53f30 <= a) -> (a + k <= DNB \/ DNB + 2 ^ 20 <= a) -> (a + k <= SSB \/ SSB + 2 ^ 23 <= a) ->
               (a + k <= B + -144 - 224 \/ B + -144 <= a) ->
               disjoint_from [(AB + rz_size n + -16, AB + rz_size n); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
                              (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (B + -144 - 224, B + -144)] a k).
  { intros a k Hk X1 X2 X3 X4 X5. cbn [disjoint_from].
    split; [exact X1|]. split; [clear X1 X3 X4 X5; destruct X2; lia|].
    split; [clear X1 X3 X4 X5; destruct X2; lia|]. split; [exact X3|]. split; [clear X1 X3 X4 X5; destruct X2; lia|].
    split; [clear X1 X3 X4 X5; destruct X2; lia|]. split; [exact X4|]. split; [exact X5 | exact I]. }
  apply (sl_p2S Q HK m3 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           (firstn 1 hdr) (hb1 (hdr_b1 hdr)) (Z_to_bv 64 (snd (depot_put D tr)))).
  - eapply (munch_weaken _ _ m2 m3); [|exact MU3]. intros x Hx. cbn [outside]. rewrite Z1.
    split; [piece 0%nat Hx|]. split; [piece 3%nat Hx|]. split; [piece 3%nat Hx|]. split; [piece 4%nat Hx|]. split; [piece 3%nat Hx|].
    split; [piece 3%nat Hx|]. split; [piece 5%nat Hx|]. split; [piece 6%nat Hx | exact I].
  - exact WM3.
  - exact MI3.
  - exact ST3.
  - apply (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m2 m3 _ AF MU3 WM3).
    apply D3; unfold SEGTOP_A in *; try lia; sl_sep.
  - exact HB1.
  - exact HB4.
  - exact HD3.
  - exact DR3.
Qed.

End STail.
