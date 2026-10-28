(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread I_consts I_qck F_memcpy X_atexit I_memcpyw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Lemma imemcpy_dst_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at bsegs m x [b]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a5' a6' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 e) (Z_to_bv 64 e) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1bde08) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 c) (Z_to_bv 64 e) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1bddf8) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
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
Lemma imemcpy_dst_rip : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (sp + -2160) -> lo <= sp - IMEMCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 < n -> d + n < 2^63 -> s + n < 2^63 ->
  acc bsegs m d n -> rng_ok d n -> m2s_cells m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s4' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2160)) gp tp t0' t1' t2' s0 s1'
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7' s2' s3' s4' s5
                    s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1bda6c) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2240, sp - 2160)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (sp + -2160))
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1bde10) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN AC RO M2S MI.
  idtac.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2160)) = sp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 5 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 4 lstep. lstep. if_true.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma imemcpy_dst : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (sp + -2160) -> lo <= sp - IMEMCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 <= n -> d + n < 2^63 -> s + n < 2^63 ->
  chk_ok m d n -> m2s_cells m -> icells m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s4' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2160)) gp tp t0' t1' t2' s0 s1'
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7' s2' s3' s4' s5
                    s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1bda6c) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2240, sp - 2160)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (sp + -2160))
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (d + n)) s5 (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1bda24) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN (AC & QW & RO) M2S (G2 & G1 & RM & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 d) by lia.
  assert (EUnd : bv_unsigned (Z_to_bv 64 (18446744073709551615 - d)) = 18446744073709551615 - d) by (apply unsigned_lit; lia).
  if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (imemcpy_dst_rip sp d s n); try assumption; lia.
  - (* [comment removed for export] *)
    subst n. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + d ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((d / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (d + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((d + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (d + n + -1) with (d + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (d + n + -1) / 8) with ((d + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m d n AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((d + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (imemcpy_dst_rip sp d s n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (imemcpy_dst_loop (Z.to_nat ((d + n + -1) / 8 + 2147450880 - (d / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a5' & a6' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (imemcpy_dst_rip sp d s n); try assumption; lia.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

End WithRIP.
