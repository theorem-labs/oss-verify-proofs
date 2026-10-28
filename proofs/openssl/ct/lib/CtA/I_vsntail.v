(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma ivsn_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at ctasegs m x [b]) -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b2700) fc None m (seg_rom ctasegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b26f0) fc None m (seg_rom ctasegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition ivsn_pre_epi (usp r : Z) (gp tp s0 s4 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2' s3' s4 s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1b25d0) fc None m' (seg_rom ctasegs)
      /\ munch [(usp - 2240, usp - 2160)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (usp + -2160).

(* [comment removed for export] *)
Lemma ivsn_rip : forall (usp D n' r : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= D -> 0 < n' -> D + n' < 2^63 ->
  acc ctasegs m D n' -> rng_ok D n' -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (ivsn_pre_epi usp r gp tp s0 s4 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n') (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b2708) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(usp - 2240, usp - 2160)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| rewrite EUsp; lia
             | unfold kHighShadowEnd in *; lia | assumption|].
  lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 2 lstep. lstep. if_true.
  apply evt_done. unfold ivsn_pre_epi. do 21 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma ivsn_chk : forall (usp D n n' r : Z) (ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= D -> 1 <= n' < 2^31 -> D + n' < 2^63 -> 1 <= n < 2^63 ->
  chk_ok m D n' -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (ivsn_pre_epi usp r gp tp s0 s4 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n') (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b2588) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN NN (AC & QW & RO) M2S MI.
  pose proof M2S as (G1 & SHC & _).
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2240, usp - 2160)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n') = n') by (apply unsigned_lit; lia).
  assert (EUnn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n') as [BIG|SMALL].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n' + -65)) = n' - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (ivsn_rip usp D n' r); try assumption; lia.
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n' + -65)) = n' - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2. unfold SHB.
    assert (E1 : Z.land ((2147450880 + D ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((D / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (D + n' + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((D + n' - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (D + n' + -1) with (D + n' - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (D + n' + -1) / 8) with ((D + n' + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + D / 8) with (D / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m D n' AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((D + n' + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold ivsn_pre_epi. do 21 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (ivsn_rip usp D n' r); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (ivsn_loop (Z.to_nat ((D + n' + -1) / 8 + 2147450880 - (D / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold ivsn_pre_epi. do 21 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (ivsn_rip usp D n' r); try assumption; lia.
    + apply evt_done. unfold ivsn_pre_epi. do 21 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.
End WithRIP.
