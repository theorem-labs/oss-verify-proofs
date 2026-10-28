(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread I_consts I_qck X_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition pcells (m : mem) : Prop :=
  ro_cells bsegs m 0x5e0cd8 [C8 (Z_to_bv 64 0x6a39f8)] /\ ro_cells bsegs m 0x6a39f8 [C8 (Z_to_bv 64 0x7fff8000)].

(* [comment removed for export] *)
Lemma pcf_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at bsegs m x [b]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1ac4bc) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ac4ac) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

(* [comment removed for export] *)
Lemma pcs_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at bsegs m x [b]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1ac094) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ac084) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition pcrr_post (pc : Z) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 pc) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma pcf_rip : forall (usp A len : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo usp -> lo <= usp - 80 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= A -> 0 <= len -> A + len + 1 < 2^63 ->
  acc bsegs m A (len + 1) -> rng_ok A (len + 1) -> m2s_cells m -> mem_inv bsegs m ->
  evt bsegs (pcrr_post 0x1abb90 (Z_to_bv 64 usp) gp tp s0 s1 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 A) s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 A) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ac4c4) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH A0 L0 AL AC RO M2S MI.
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold pcrr_post. rewrite EUsp. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma pcf_check : forall (usp A len : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo usp -> lo <= usp - 80 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= A -> 0 <= len -> A + len + 1 < 2^63 ->
  chk_ok m A (len + 1) -> m2s_cells m -> pcells m -> mem_inv bsegs m ->
  evt bsegs (pcrr_post 0x1abb90 (Z_to_bv 64 usp) gp tp s0 s1 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 A) s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 A) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1abb44) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH A0 L0 AL (AC & QW & RO) M2S (G1 & SHC) MI.
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  assert (EUA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (EUl1 : bv_unsigned (Z_to_bv 64 (len + 1)) = len + 1) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 A) by lia.
  assert (EUnA : bv_unsigned (Z_to_bv 64 (18446744073709551615 - A)) = 18446744073709551615 - A) by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec len 64) as [SMALL|BIG].
  - (* [comment removed for export] *)
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + A ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((A / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (len + A) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((A + (len + 1) - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (A + (len + 1) - 1) with (len + A) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (len + A) / 8) with ((A + (len + 1) - 1) / 8 + 2147450880) by (replace (A + (len + 1) - 1) with (len + A) by lia; lia).
      replace (2147450880 + A / 8) with (A / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m A (len + 1) AC ltac:(lia) A0) as SB. unfold shad, SHB in SB.
      destruct (SB ((A + (len + 1) - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold pcrr_post. rewrite EUsp. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (pcf_rip usp A len); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (pcf_loop (Z.to_nat ((A + (len + 1) - 1) / 8 + 2147450880 - (A / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold pcrr_post. rewrite EUsp. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (pcf_rip usp A len); try assumption; lia.
    + apply evt_done. unfold pcrr_post. rewrite EUsp. do 17 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    if_true. lstep. if_true.
    apply (pcf_rip usp A len); try assumption; lia.
Qed.
(* [comment removed for export] *)
Lemma pcs_rip : forall (usp S n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo usp -> lo <= usp - 80 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= S -> 0 < n -> S + n < 2^63 ->
  acc bsegs m S n -> rng_ok S n -> m2s_cells m -> mem_inv bsegs m ->
  evt bsegs (pcrr_post 0x1abf74 (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 (Z_to_bv 64 S) (Z_to_bv 64 n) s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 S) (Z_to_bv 64 n) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ac09c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH S0 N0 SN AC RO M2S MI.
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold pcrr_post. rewrite EUsp. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma pcs_check : forall (usp S n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo usp -> lo <= usp - 80 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= S -> 0 < n -> S + n < 2^63 ->
  chk_ok m S n -> m2s_cells m -> pcells m -> mem_inv bsegs m ->
  evt bsegs (pcrr_post 0x1abf74 (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 (Z_to_bv 64 S) (Z_to_bv 64 n) s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 S) (Z_to_bv 64 n) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ac018) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH S0 N0 SN (AC & QW & RO) M2S (G1 & SHC) MI.
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 S) by lia.
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - S)) = 18446744073709551615 - S) by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (pcs_rip usp S n); try assumption; lia.
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + S ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((S / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (S + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((S + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (S + n + -1) with (S + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + apply evt_done. unfold pcrr_post. rewrite EUsp. do 17 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (S + n + -1) / 8) with ((S + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + S / 8) with (S / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m S n AC ltac:(lia) S0) as SB. unfold shad, SHB in SB.
      destruct (SB ((S + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold pcrr_post. rewrite EUsp. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (pcs_rip usp S n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (pcs_loop (Z.to_nat ((S + n + -1) / 8 + 2147450880 - (S / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold pcrr_post. rewrite EUsp. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (pcs_rip usp S n); try assumption; lia.
Qed.
End WithRIP.
