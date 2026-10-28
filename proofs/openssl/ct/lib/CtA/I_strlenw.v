(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_strnlenw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma istrlen_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at ctasegs m x [b]) -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (a0' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1ad8d8) fc None m (seg_rom ctasegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ad8c8) fc None m (seg_rom ctasegs)).
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
Lemma istrlen_rip : forall (sp p r : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  acc ctasegs m p (r + 1) -> rng_ok p (r + 1) -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1ad7d0) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (r + 1)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 (Z_to_bv 64 r) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ad8e0) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true. lstep. lstep.
  apply evt_done. do 22 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma istrlen_chk : forall (sp p r : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  s0 = Z_to_bv 64 sp ->
  stk ctasegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  chk_ok m p (r + 1) -> m2s_cells m -> icells_sn m -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1ad7d0) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ad77c) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros -> ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S (G70 & G2 & RM & RS & SHC & AI & ISL) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. if_false. lstep. lstep.
  destruct (Z_lt_le_dec r 64) as [SMALL|BIG].
  - (* [comment removed for export] *)
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (r + p) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + (r + 1) - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + (r + 1) - 1) with (r + p) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (r + p) / 8) with ((p + (r + 1) - 1) / 8 + 2147450880) by (replace (p + (r + 1) - 1) with (r + p) by lia; lia).
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p (r + 1) AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + (r + 1) - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 7 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- lstep. lstep.
           apply evt_done. do 22 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (istrlen_rip sp p r); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (istrlen_loop (Z.to_nat ((p + (r + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a0' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- lstep. lstep.
           apply evt_done. do 22 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (istrlen_rip sp p r); try assumption; lia.
    + apply evt_done. do 22 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    if_true. lstep. lstep. if_true.
    apply (istrlen_rip sp p r); try assumption; lia.
Qed.
End WithRIP.
