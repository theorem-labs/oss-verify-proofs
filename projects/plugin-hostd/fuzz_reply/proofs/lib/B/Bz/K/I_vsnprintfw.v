(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: Image B twin of lib/A/Bz/K/I_vsnprintfw.v at d49bd1db505: lib/B/Bz/K/I_vsnprintfw.v at 3da0143047f (= 891ad39df4c) with its stack floor `0x5f7000 <= lo` (fuzz_state's image top) set to fuzz_reply.asan-ubsan's top 0x5fc000 (3x), as lib/A has fuzz_reply.asan's top 0x5fb000; every other numeral equals the A text's, moved by symbol + offset (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.K Require Import I_vprintfw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma vsnprintf_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x46764) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46754) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition vsnprintf_pre_epi (usp r : Z) (gp tp s0 s4 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2' s3' s4 s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x46634) fc None m' (seg_rom asegs)
      /\ munch [(usp - 2240, usp - 2160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2160).

(* [comment removed for export] *)
Lemma vsnprintf_rip : forall (usp D n' r : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= D -> 0 < n' -> D + n' < 2^63 ->
  acc asegs m D n' -> rng_ok D n' -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (vsnprintf_pre_epi usp r gp tp s0 s4 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n') (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4676c) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(usp - 2240, usp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| rewrite EUsp; lia
             | unfold kHighShadowEnd in *; lia | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 2 lstep. lstep. if_true.
  apply evt_done. unfold vsnprintf_pre_epi. do 21 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma vsnprintf_chk : forall (usp D n n' r : Z) (ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= D -> 1 <= n' < 2^31 -> D + n' < 2^63 -> 1 <= n < 2^63 ->
  chk_ok m D n' -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (vsnprintf_pre_epi usp r gp tp s0 s4 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n') (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x465ec) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN NN (AC & QW & RO) M2S MI.
  pose proof M2S as (G1 & SHC & _).
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2240, usp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n') = n') by (apply unsigned_lit; lia).
  assert (EUnn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n') as [BIG|SMALL].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n' + -65)) = n' - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (vsnprintf_rip usp D n' r); try assumption; lia.
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
        -- apply evt_done. unfold vsnprintf_pre_epi. do 21 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (vsnprintf_rip usp D n' r); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (vsnprintf_loop (Z.to_nat ((D + n' + -1) / 8 + 2147450880 - (D / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold vsnprintf_pre_epi. do 21 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (vsnprintf_rip usp D n' r); try assumption; lia.
    + apply evt_done. unfold vsnprintf_pre_epi. do 21 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.
Definition vsnprintf_ret (usp r lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(usp - 2240, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp.

Lemma vsnprintf_tail : forall (usp D n n' r lo : Z) (j8 junk : list byte)
    (Vw ra' ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s4' s5' s6' s7' s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 ->
  rw_cells asegs m (usp + -96) [C8 Vw; C8 Vw; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2160) [CB 2064 junk] ->
  0 <= r -> 0 <= D -> 1 <= n' < 2^31 -> D + n' < 2^63 -> 1 <= n < 2^63 ->
  chk_ok m D n' -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (vsnprintf_ret usp r lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 n') (Z_to_bv 64 r)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 D) (Z_to_bv 64 n) s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x465ec) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH FRt FRb R0 D0 N0 DN NN CHK M2S MI.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - 2240, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { apply (vsnprintf_chk usp D n n' r);
      first [exact ST | exact CHK | exact M2S | exact MI | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms' P. unfold vsnprintf_pre_epi in P.
  destruct P as (m1 & ra1 & u0 & u1 & u2 & u3 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11
                 & -> & MU1 & WM1 & MI1 & ST1).
  pose proof (rw_cells_transport asegs _ _ _ _ _ FRt MU1 WM1
                ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                      repeat split; try lia; try exact I)) as FRt1.
  pose proof (rw_cells_transport asegs _ _ _ _ _ FRb MU1 WM1
                ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                      repeat split; try lia; try exact I)) as FRb1.
  clear FRt FRb ST. rename ST1 into ST.
  assert (MU2 : munch [(usp - 2240, usp)] m m1)
    by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros ?x ?Hx; split; [lia| exact I]).
  assert (WM2 : wmono asegs m m1) by exact (wmono_trans _ _ _ _ WM WM1).
  clear MU MU1 WM WM1. rename MU2 into MU. rename WM2 into WM.
  lstep.
  release_frame FRb1 ST (usp + -96).
  do 11 lstep.
  release_frame FRt1 ST usp.
  apply evt_done. unfold vsnprintf_ret. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma vsnprintf_walkC : forall (usp D n r lo : Z) (j8 junk : list byte)
    (ra' ra gp tp t0 t1 t2 s0 s1 s1' s2 s3 s4 s5 s6 s7 s4' s5' s6' s7' s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Vw : word)
    F fc (m : mem),
  stk asegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 ->
  rw_cells asegs m (usp + -96) [C8 Vw; C8 Vw; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2160) [CB 2064 junk] ->
  0 <= r -> r + 1 < 2^31 -> 1 <= n < 2^31 -> 0 <= D -> D + r + 1 < 2^47 -> D + n < 2^47 ->
  chk_ok m D (Z.min n (r + 1)) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (vsnprintf_ret usp r lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1' (Z_to_bv 64 r)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 D) (Z_to_bv 64 n) s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x465cc) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH FRt FRb R0 R31 NN D0 DRH DNH CHK M2S MI.
  unfold kHighShadowEnd in LOLO.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (ESr : bv_signed (Z_to_bv 64 r) = r).
  { unfold bv_signed. rewrite EUr. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia. }
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  assert (EUnd : bv_unsigned (Z_to_bv 64 (18446744073709551615 - D)) = 18446744073709551615 - D)
    by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep. lstep.
  rewrite (bv_swrap_small 32 (r + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
  destruct (Z_lt_le_dec r n) as [FULL|TRUNC].
  - if_true.
    lstep. lstep. rewrite (lxor_ones64 D) by lia.
    lstep. lstep. lstep. if_true.
    replace (Z.min n (r + 1)) with (r + 1) in CHK by lia.
    apply (vsnprintf_tail usp D n (r + 1) r lo j8 junk Vw); try assumption; lia.
  - if_false.
    lstep. rewrite (lxor_ones64 D) by lia.
    lstep. lstep. lstep. if_false.
    replace (Z.min n (r + 1)) with n in CHK by lia.
    apply (vsnprintf_tail usp D n n r lo j8 junk Vw); try assumption; lia.
Qed.

End WithRIP.

Definition vsncells (m : mem) : Prop := ro_cells asegs m 0x9fcf0 [C8 (Z_to_bv 64 0x963b4)].

Definition vsnwA1_post (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 b3 b4 b5 b6 b7 t3 t4 t5 t6 : word) (j8 junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x465b0) (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) a2
                  (Z_to_bv 64 0x17944) a2 a3 b3 b4 b5 b6 b7
                  a0 a1 (Z_to_bv 64 0x138168) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x459bc) fc None m' (seg_rom asegs)
    /\ munch [(usp - 2176, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2160)
    /\ rw_cells asegs m' (usp + -96) [C8 a3; C8 a3; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (usp + -2160) [CB 2064 junk].

Lemma vsnprintf_walkA1 : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 2176 -> 0x5fc000 <= lo -> usp <= 2^47 -> pfcells m -> mem_inv asegs m ->
  evt asegs (vsnwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4222c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH PFC MI.
  pose proof (munch_refl [(usp - 2176, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 96%nat ST. rename FR into FRt.
  carve_frame 2064%nat ST. rename FR into FRb.
  apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRt; [| reflexivity].
  cbn [mk_CB_cells app] in FRt.
  xsteps_to 0x5ae48%Z.
  call try_init_spec; [exact AI | rewrite EU2160; exact ST | rewrite EU2160; lia | lia | assumption |].
  rename POST into ST. rewrite EU2160 in ST.
  xsteps_to 0x459bc%Z.
  apply evt_done. unfold vsnwA1_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRt| exact FRb].
Qed.

Lemma vsnprintf_walkA2 : forall (usp : Z) (j8 : list byte)
    (v c0 c1 c2 c3 c4 c5 c6 c7 ra0 : word)
    ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m (usp + -96) [C8 v; C8 v; CB 8 j8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 ra0] ->
  ro_cells asegs m 0x9fcf0 [C8 (Z_to_bv 64 0x963b4)] ->
  usp <= 2^47 -> 2160 <= usp -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (b4 : word), ms' =
      MS (mkR (Z_to_bv 64 0x465cc) (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 s2 s3 s1 v b4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x963b4) fc None m (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x465b0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros FRv RVS SPH SPL MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  do 7 lstep.
  apply evt_done. eexists. reflexivity.
Qed.

Definition vsnprintf_at_call (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 b4 b5 b6 b7 t3 t4 t5 t6 : word) (j8 junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x465cc) (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) a2
                  a0 a1 a2 a3 b4 b5 b6 b7
                  a0 a1 (Z_to_bv 64 0x138168) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x963b4) fc None m' (seg_rom asegs)
    /\ munch [(usp - 4480, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2160)
    /\ rw_cells asegs m' (usp + -96) [C8 a3; C8 a3; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (usp + -2160) [CB 2064 junk].

Definition vsnpfcells (m : mem) : Prop :=
  rw_cells asegs m 0xa7318 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x9df40 [C8 (Z_to_bv 64 0x138168)]
  /\ ro_cells asegs m 0x1381bc [C1 (Z_to_bv 8 1)].

Lemma vsnprintf_walkA1c : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 2176 -> 0x5fc000 <= lo -> usp <= 2^47 -> vsnpfcells m -> mem_inv asegs m ->
  evt asegs (vsnwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4222c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH PFC MI.
  pose proof (munch_refl [(usp - 2176, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  destruct PFC as (AI & GCF & CPF).
  carve_frame 96%nat ST. rename FR into FRt.
  carve_frame 2064%nat ST. rename FR into FRb.
  apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRt; [| reflexivity].
  cbn [mk_CB_cells app] in FRt.
  xsteps_to 0x5ae48%Z.
  call try_init_spec; [exact AI | rewrite EU2160; exact ST | rewrite EU2160; lia | lia | assumption |].
  rename POST into ST. rewrite EU2160 in ST.
  xsteps_to 0x459bc%Z.
  apply evt_done. unfold vsnwA1_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRt| exact FRb].
Qed.

Lemma vsnprintf_walkAc : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 2176 -> 0x5fc000 <= lo -> usp <= 2^47 ->
  vsnpfcells m -> vsncells m -> mem_inv asegs m ->
  (forall (m1 : mem) (t0' t1' t2' b3 b4 b5 b6 b7 t3' t4' t5' t6' : word),
     munch [(usp - 2176, usp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -2160) ->
     evt asegs (pcom_post (Z_to_bv 64 0x465b0) (Z_to_bv 64 (usp + -2160)) gp tp (Z_to_bv 64 usp) a2 a0 a1
                  (Z_to_bv 64 0x138168) s5 s6 s7 s8 s9 s10 s11 F fc lo m1)
       (MS (mkR (Z_to_bv 64 0x465b0) (Z_to_bv 64 (usp + -2160)) gp tp t0' t1' t2' (Z_to_bv 64 usp) a2
                (Z_to_bv 64 0x17944) a2 a3 b3 b4 b5 b6 b7 a0 a1 (Z_to_bv 64 0x138168) s5 s6 s7 s8 s9 s10 s11
                t3' t4' t5' t6')
           F (Z_to_bv 64 0x459bc) fc None m1 (seg_rom asegs))) ->
  evt asegs (vsnprintf_at_call usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4222c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH PFC VSN MI PC.
  unfold vsncells in VSN.
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  eapply evt_cut; [apply (vsnprintf_walkA1c usp lo); [exact ST | exact LO | exact LOLO | exact SPH | exact PFC | exact MI] |].
  intros ms1 H1. unfold vsnwA1_post in H1.
  destruct H1 as (m1 & u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & j8 & junk & -> & MU1 & WM1 & MI1
                  & ST1 & FRt1 & FRb1).
  assert (VSN1 : ro_cells asegs m1 0x9fcf0 [C8 (Z_to_bv 64 0x963b4)]).
  { apply (ro_cells_transport asegs _ m m1 _ _ VSN MU1).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  eapply evt_cut; [exact (PC m1 u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MU1 WM1 MI1 ST1) |].
  intros ms2 H2. unfold pcom_post in H2.
  destruct H2 as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite EU2160 in MU2, ST2.
  assert (FRt2 : rw_cells asegs m2 (usp + -96)
                   [C8 a3; C8 a3; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport asegs _ m1 m2 _ _ FRt1 MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  assert (FRb2 : rw_cells asegs m2 (usp + -2160) [CB 2064 junk]).
  { apply (rw_cells_transport asegs _ m1 m2 _ _ FRb1 MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  assert (VSN2 : ro_cells asegs m2 0x9fcf0 [C8 (Z_to_bv 64 0x963b4)]).
  { apply (ro_cells_transport asegs _ m1 m2 _ _ VSN1 MU2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  replace (ret_pc (Z_to_bv 64 0x465b0)) with (Z_to_bv 64 0x465b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  eapply evt_cut; [apply (vsnprintf_walkA2 usp j8 a3 s0 s1 s2 s3 s4 s5 s6 s7 ra);
                   [exact FRt2 | exact VSN2 | exact SPH | lia | exact MI2] |].
  intros ms3 (b4' & ->).
  apply evt_done. unfold vsnprintf_at_call. exists m2. do 11 eexists. exists j8. exists junk.
  split; [reflexivity|].
  split.
  { apply (munch_trans [(usp - 4480, usp)] m m1 m2).
    - eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
    - eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2|].
  split; [exact FRt2| exact FRb2].
Qed.

Section WithPC.
Variable pc_pre : word -> word -> mem -> Prop.
Hypothesis PCOM : pcom_stmt pc_pre.

Lemma vsnprintf_walkA : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 4480 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
  pfcells m -> vsncells m ->
  (forall m', munch [(usp - 2176, usp)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> pc_pre a2 a3 m') ->
  mem_inv asegs m ->
  evt asegs (vsnprintf_at_call usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4222c) fc None m (seg_rom asegs)).
Proof using PCOM.
  intros until m. intros ST LO LOLO SPH S16 PFC VSN PRE MI.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO'.
  unfold vsncells in VSN.
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  eapply evt_cut; [apply (vsnprintf_walkA1 usp lo); [exact ST | lia | lia | exact SPH | exact PFC | exact MI] |].
  intros ms1 H1. unfold vsnwA1_post in H1.
  destruct H1 as (m1 & u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & j8 & junk & -> & MU1 & WM1 & MI1
                  & ST1 & FRt1 & FRb1).
  pose proof (PRE m1 MU1 WM1 MI1) as PRE1.
  assert (VSN1 : ro_cells asegs m1 0x9fcf0 [C8 (Z_to_bv 64 0x963b4)]).
  { apply (ro_cells_transport asegs _ m m1 _ _ VSN MU1).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  pose proof PCOM as PC. unfold pcom_stmt in PC.
  eapply evt_cut.
  { apply PC with (lo := lo);
      [ rewrite EU2160; exact ST1 | rewrite EU2160; lia | exact LOLO | rewrite EU2160; lia
      | rewrite EU2160; Z.div_mod_to_equations; lia | exact PRE1 | exact MI1 ]. }
  intros ms2 H2. unfold pcom_post in H2.
  destruct H2 as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite EU2160 in MU2, ST2.
  assert (FRt2 : rw_cells asegs m2 (usp + -96)
                   [C8 a3; C8 a3; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport asegs _ m1 m2 _ _ FRt1 MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  assert (FRb2 : rw_cells asegs m2 (usp + -2160) [CB 2064 junk]).
  { apply (rw_cells_transport asegs _ m1 m2 _ _ FRb1 MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  assert (VSN2 : ro_cells asegs m2 0x9fcf0 [C8 (Z_to_bv 64 0x963b4)]).
  { apply (ro_cells_transport asegs _ m1 m2 _ _ VSN1 MU2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  replace (ret_pc (Z_to_bv 64 0x465b0)) with (Z_to_bv 64 0x465b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  eapply evt_cut; [apply (vsnprintf_walkA2 usp j8 a3 s0 s1 s2 s3 s4 s5 s6 s7 ra);
                   [exact FRt2 | exact VSN2 | exact SPH | lia | exact MI2] |].
  intros ms3 (b4' & ->).
  apply evt_done. unfold vsnprintf_at_call. exists m2. do 11 eexists. exists j8. exists junk.
  split; [reflexivity|].
  split.
  { apply (munch_trans [(usp - 4480, usp)] m m1 m2).
    - eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
    - eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2|].
  split; [exact FRt2| exact FRb2].
Qed.
End WithPC.

Section WithRIPm.
Hypothesis RIP : rip_stmt.

Lemma vsnprintf_walkCm : forall (usp D n r lo : Z) (j8 junk : list byte)
    (ra' ra gp tp t0 t1 t2 s0 s1 s1' s2 s3 s4 s5 s6 s7 s4' s5' s6' s7' s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Vw : word)
    F fc (m : mem),
  stk asegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 ->
  rw_cells asegs m (usp + -96) [C8 Vw; C8 Vw; CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2160) [CB 2064 junk] ->
  0 <= r -> r + 1 < 2^31 -> 1 <= n < 2^31 -> 0 <= D -> D + Z.min n (r + 1) <= 2^47 ->
  chk_ok m D (Z.min n (r + 1)) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (vsnprintf_ret usp r lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1' (Z_to_bv 64 r)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 D) (Z_to_bv 64 n) s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x465cc) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH FRt FRb R0 R31 NN D0 DMH CHK M2S MI.
  unfold kHighShadowEnd in LOLO.
  assert (DM1 : D + 1 <= 2^47) by lia.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (ESr : bv_signed (Z_to_bv 64 r) = r).
  { unfold bv_signed. rewrite EUr. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia. }
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  assert (EUnd : bv_unsigned (Z_to_bv 64 (18446744073709551615 - D)) = 18446744073709551615 - D)
    by (apply unsigned_lit; lia).
  destruct (Z_lt_le_dec r n) as [FULL|TRUNC].
  - assert (DRH : D + r + 1 <= 2^47) by lia.
    replace (Z.min n (r + 1)) with (r + 1) in CHK by lia. clear DMH.
    lstep. if_false.
    lstep. lstep. lstep.
    rewrite (bv_swrap_small 32 (r + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
    if_true.
    lstep. lstep. rewrite (lxor_ones64 D) by lia.
    lstep. lstep. lstep. if_true.
    apply (vsnprintf_tail RIP usp D n (r + 1) r lo j8 junk Vw); try assumption; lia.
  - assert (DNH : D + n <= 2^47) by lia.
    replace (Z.min n (r + 1)) with n in CHK by lia. clear DMH.
    lstep. if_false.
    lstep. lstep. lstep.
    rewrite (bv_swrap_small 32 (r + 1)) by (change (bv_half_modulus 32) with (2^31); lia).
    if_false.
    lstep. rewrite (lxor_ones64 D) by lia.
    lstep. lstep. lstep. if_false.
    apply (vsnprintf_tail RIP usp D n n r lo j8 junk Vw); try assumption; lia.
Qed.

End WithRIPm.
