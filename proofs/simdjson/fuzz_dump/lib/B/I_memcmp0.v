(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_memchrw F_memcmp I_memcmpw I_memcmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition cmp_post0 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - D, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Definition cmp_fn0 (entry D : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p q : Z) (lo : Z),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 0 -> 0 <= p < 2^64 -> 0 <= q < 2^64 ->
  m2s_cells m -> icells_cmp m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - D -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  evt bsegs (cmp_post0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Lemma cmp_fn0_musl : cmp_fn0 0x160854 0.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q lo
    -> -> -> PR QR M2S IC MI ST LO LOLO SPH.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep. if_true. lstep. lstep.
  apply evt_done. unfold cmp_post0.
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Section Common0.
Hypothesis RIP : rip_stmt.
Variables (real D : Z).
Hypothesis REAL_rng : 0 <= real < 2^47.
Hypothesis REAL_even : real mod 2 = 0.
Hypothesis D_pos : 0 <= D.
Hypothesis CALLEE : cmp_fn0 real D.

Lemma icmp_common0_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p q : Z) (lo : Z),
  a1 = Z_to_bv 64 real -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 q -> a4 = Z_to_bv 64 0 -> 0 <= p < 2^64 -> 0 <= q < 2^64 ->
  m2s_cells m -> icells_cmp m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - (CMPC_DEPTH + D) -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  evt bsegs (cmp_post0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (CMPC_DEPTH + D) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6b1fc) fc None m (seg_rom bsegs)).
Proof using RIP REAL_rng REAL_even D_pos CALLEE.
  intros until lo. intros -> -> -> -> PR QR M2S IC MI ST LO LOLO SPH.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2272 + D), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  pose proof M2S as (M2a & M2b & M2c).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 real) = real) by (apply unsigned_lit; lia).
  assert (EU2192 : bv_unsigned (Z_to_bv 64 (usp + -2192)) = usp + -2192) by (apply unsigned_lit; lia).
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  assert (EUnq : bv_unsigned (Z_to_bv 64 (18446744073709551615 - q)) = 18446744073709551615 - q) by (apply unsigned_lit; lia).
  assert (EU65 : bv_unsigned (Z_to_bv 64 (0 + -65)) = 0 - 65 + 2^64)
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; reflexivity).
  assert (EU65b : bv_unsigned (Z_to_bv 64 (-65)) = -65 + 2^64)
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; reflexivity).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2088%nat ST.
  do 14 lstep.
  do 7 lstep.
  do 2 lstep. lstep. lstep. if_false. lstep. lstep. lstep. lstep. if_false.

  lstep. rewrite (lxor_ones64 p) by lia. lstep. if_false.
  lstep. lstep. lstep. if_true. lstep. if_false. lstep.

  lstep. rewrite (lxor_ones64 q) by lia. lstep. if_false.
  lstep. lstep. if_true. lstep. if_false. lstep.
  lazymatch goal with H : stk bsegs _ lo (usp + -2192) |- _ => rename H into ST3 | _ => idtac end.
  do 3 lstep. lstep.
  rewrite (ret_pc_even real) by (lia || exact REAL_even).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (M2S3 : m2s_cells mm) by (split; [| split]; assumption);
    assert (IC3 : icells_cmp mm) by (split; [| split; [| split; [| split; [| split]]]]; assumption)
  end.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply CALLEE with (lo := lo) (p := p) (q := q) | post_call segs mm] end;
              [reflexivity| reflexivity| reflexivity| exact PR| exact QR| exact M2S3| exact IC3| assumption
               | rewrite EU2192; assumption| rewrite EU2192; lia| unfold kHighShadowEnd; lia| rewrite EU2192; lia|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2192 in H; rename H into ST4 end.
  do 2 lstep. do 5 lstep. lstep. lstep. lstep. lstep. do 13 lstep. lstep.
  release_frame FR ST4 (usp + -104). release_frame FRs ST4 usp.
  lstep.
  unfold cmp_post0. sys_finish.
  - rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  - rewrite EU. assumption.
Qed.

End Common0.

Section Shellimemcmp0.
Hypothesis RIP : rip_stmt.
Variable D : Z.
Hypothesis D_pos : 0 <= D.
Hypothesis CALLEE : cmp_fn0 0x160854 D.

Lemma imemcmp_shell0_spec : cmp_fn0 0x6ba90 (2320 + D).
Proof using RIP D_pos CALLEE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q lo
    -> -> -> PR QR M2S IC MI ST LO LOLO SPH.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2320 + D), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  pose proof M2S as (M2a & M2b & M2c).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  do 9 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. do 4 lstep.
  call try_init_spec; [assumption| rewrite EU48; exact ST| rewrite EU48; lia| rewrite ?EU48; lia| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false. do 6 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (M2S3 : m2s_cells mm) by (split; [| split]; assumption);
    assert (IC3 : icells_cmp mm) by (split; [| split; [| split; [| split; [| split]]]]; assumption)
  end.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply (icmp_common0_spec RIP 0x160854 D ltac:(lia) eq_refl D_pos CALLEE) with (lo := lo) (p := p) (q := q)
                    | post_call segs mm] end;
    [reflexivity| reflexivity| reflexivity| reflexivity| exact PR| exact QR| exact M2S3| exact IC3| assumption
    | rewrite EU48; exact ST2| rewrite EU48; lia| unfold kHighShadowEnd; lia| rewrite EU48; lia|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST4 end.
  do 5 lstep.
  release_frame FR ST4 usp.
  lstep.
  unfold cmp_post0. sys_finish.
  - rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  - rewrite EU. assumption.
Qed.
End Shellimemcmp0.

Section Shellibcmp0.
Hypothesis RIP : rip_stmt.
Variable D : Z.
Hypothesis D_pos : 0 <= D.
Hypothesis CALLEE : cmp_fn0 0x160784 D.

Lemma ibcmp_shell0_spec : cmp_fn0 0x6bb4c (2320 + D).
Proof using RIP D_pos CALLEE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q lo
    -> -> -> PR QR M2S IC MI ST LO LOLO SPH.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2320 + D), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  pose proof M2S as (M2a & M2b & M2c).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  do 9 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. do 4 lstep.
  call try_init_spec; [assumption| rewrite EU48; exact ST| rewrite EU48; lia| rewrite ?EU48; lia| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false. do 6 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (M2S3 : m2s_cells mm) by (split; [| split]; assumption);
    assert (IC3 : icells_cmp mm) by (split; [| split; [| split; [| split; [| split]]]]; assumption)
  end.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply (icmp_common0_spec RIP 0x160784 D ltac:(lia) eq_refl D_pos CALLEE) with (lo := lo) (p := p) (q := q)
                    | post_call segs mm] end;
    [reflexivity| reflexivity| reflexivity| reflexivity| exact PR| exact QR| exact M2S3| exact IC3| assumption
    | rewrite EU48; exact ST2| rewrite EU48; lia| unfold kHighShadowEnd; lia| rewrite EU48; lia|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST4 end.
  do 5 lstep.
  release_frame FR ST4 usp.
  lstep.
  unfold cmp_post0. sys_finish.
  - rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  - rewrite EU. assumption.
Qed.
End Shellibcmp0.

Section Top0.
Hypothesis RIP : rip_stmt.

Lemma cmp_fn0_musl_bcmp : cmp_fn0 0x160784 2320.
Proof using RIP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q lo
    E0 E1 E2 PR QR M2S IC MI ST LO LOLO SPH.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep. lstep.
  exact (imemcmp_shell0_spec RIP 0 ltac:(lia) cmp_fn0_musl ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p q lo E0 E1 E2 PR QR M2S IC MI ST LO LOLO SPH).
Qed.

Theorem ibcmp0_spec : cmp_fn0 0x69f68 4640.
Proof using RIP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q lo
    E0 E1 E2 PR QR M2S IC MI ST LO LOLO SPH.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep.
  exact (ibcmp_shell0_spec RIP 2320 ltac:(lia) cmp_fn0_musl_bcmp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p q lo E0 E1 E2 PR QR M2S IC MI ST LO LOLO SPH).
Qed.
End Top0.
