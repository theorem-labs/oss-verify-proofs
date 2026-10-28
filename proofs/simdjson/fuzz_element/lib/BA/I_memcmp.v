(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import X_atexit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_ikit I_memchrw F_memcmp I_memcmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition icells_cmp (m : mem) : Prop :=
  ro_cells asegs m 0x16a220 [C8 (Z_to_bv 64 0x205768)]
  /\ ro_cells asegs m 0x16a230 [C8 (Z_to_bv 64 0x173c38)]
  /\ ro_cells asegs m 0x16c078 [C8 (Z_to_bv 64 0x15c4f4); C8 (Z_to_bv 64 0x15c424)]
  /\ ro_cells asegs m 0x173c38 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0x174918 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x205866 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].

Definition cmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (bp bq : list byte) (D lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - D, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ (r = Z_to_bv 64 0 <-> bp = bq).

Definition cmp_fn (entry D : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) ->
  length bq = length bp -> (0 < length bp)%nat -> 0 < p -> 0 < q ->
  p + Z.of_nat (length bp) <= 2^47 -> q + Z.of_nat (length bp) <= 2^47 ->
  bytes_at asegs m p bp -> bytes_at asegs m q bq ->
  (p + Z.of_nat (length bp) <= lo \/ bv_unsigned sp <= p) -> (q + Z.of_nat (length bp) <= lo \/ bv_unsigned sp <= q) ->
  chk_ok m p (Z.of_nat (length bp)) -> chk_ok m q (Z.of_nat (length bp)) -> m2s_cells m -> icells_cmp m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - D -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  evt asegs (cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bp bq D lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma cmp_fn_musl : cmp_fn 0x15c4f4 0.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo
    -> -> -> LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH.
  eapply evt_mono.
  { apply (memcmp_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq eq_refl eq_refl eq_refl LEN); try assumption; lia. }
  intros ms' (r & a1' & a2' & a3' & a4' & -> & HR).
  exists r, t0, t1, t2, a1', a2', a3', a4', a5, a6, a7, t3, t4, t5, t6, m.
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST| exact HR].
Qed.

Section Common.
Hypothesis RIP : rip_stmt.
Variables (real D : Z).
Hypothesis REAL_rng : 0 <= real < 2^47.
Hypothesis REAL_even : real mod 2 = 0.
Hypothesis D_pos : 0 <= D.
Hypothesis CALLEE : cmp_fn real D.

Lemma icmp_common_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  a1 = Z_to_bv 64 real -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 q -> a4 = Z_to_bv 64 (Z.of_nat (length bp)) ->
  length bq = length bp -> (0 < length bp)%nat -> 0 < p -> 0 < q ->
  p + Z.of_nat (length bp) <= 2^47 -> q + Z.of_nat (length bp) <= 2^47 ->
  bytes_at asegs m p bp -> bytes_at asegs m q bq ->
  (p + Z.of_nat (length bp) <= lo \/ bv_unsigned sp <= p) -> (q + Z.of_nat (length bp) <= lo \/ bv_unsigned sp <= q) ->
  chk_ok m p (Z.of_nat (length bp)) -> chk_ok m q (Z.of_nat (length bp)) -> m2s_cells m -> icells_cmp m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - (CMPC_DEPTH + D) -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  evt asegs (cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bp bq (CMPC_DEPTH + D) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6dc7c) fc None m (seg_rom asegs)).
Proof using RIP REAL_rng REAL_even D_pos CALLEE.
  intros until lo. intros -> -> -> -> LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bp)) in *.
  assert (N1 : 1 <= n) by (unfold n; lia).
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2272 + D), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  pose proof M2S as (M2a & M2b & M2c).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 real) = real) by (apply unsigned_lit; lia).
  assert (EU2192 : bv_unsigned (Z_to_bv 64 (usp + -2192)) = usp + -2192) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2088%nat ST.
  do 14 lstep.
  do 7 lstep.
  do 2 lstep. lstep. lstep. if_false. lstep. lstep. lstep. lstep. if_false.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CP1 : chk_ok mm p n)
      by (apply (chk_ok_agree m mm p _ CP ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (M2S1 : m2s_cells mm) by (split; [| split]; assumption);
    assert (ICQ1 : icells_cq mm) by (split; assumption)
  end.
  call (icmp_chk1 RIP usp p n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CP1| exact M2S1| exact ICQ1| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST2 end.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CQ2 : chk_ok mm q n)
      by (apply (chk_ok_agree m mm q _ CQ ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (M2S2 : m2s_cells mm) by (split; [| split]; assumption);
    assert (ICQ2 : icells_cq mm) by (split; assumption)
  end.
  call (icmp_chk2 RIP usp q n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CQ2| exact M2S2| exact ICQ2| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST3 end.
  do 3 lstep. lstep.
  rewrite (ret_pc_even real) by (lia || exact REAL_even).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CP3 : chk_ok mm p n)
      by (apply (chk_ok_agree m mm p _ CP ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (CQ3 : chk_ok mm q n)
      by (apply (chk_ok_agree m mm q _ CQ ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (M2S3 : m2s_cells mm) by (split; [| split]; assumption);
    assert (IC3 : icells_cmp mm) by (split; [| split; [| split; [| split; [| split]]]]; assumption)
  end.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply CALLEE with (lo := lo) (p := p) (q := q) (bp := bp) (bq := bq) | post_call segs mm] end;
              [reflexivity| reflexivity| reflexivity| exact LEN| exact NZ| exact P0| exact Q0| exact PH| exact QH| assumption| assumption
               | rewrite EU2192; fold n; lia| rewrite EU2192; fold n; lia| exact CP3| exact CQ3| exact M2S3| exact IC3| assumption
               | rewrite EU2192; exact ST3| rewrite EU2192; lia| unfold kHighShadowEnd; lia| rewrite EU2192; lia|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2192 in H; rename H into ST4 end.
  do 2 lstep. do 5 lstep. lstep. lstep. lstep. lstep. do 13 lstep. lstep.
  release_frame FR ST4 (usp + -104). release_frame FRs ST4 usp.
  lstep.
  unfold cmp_post. sys_finish.
  - rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  - rewrite EU. assumption.
Qed.

End Common.

Section Shellimemcmp.
Hypothesis RIP : rip_stmt.
Variable D : Z.
Hypothesis D_pos : 0 <= D.
Hypothesis CALLEE : cmp_fn 0x15c4f4 D.

Lemma imemcmp_shell_spec : cmp_fn 0x6e510 (2320 + D).
Proof using RIP D_pos CALLEE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo
    -> -> -> LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bp)) in *.
  assert (N1 : 1 <= n) by (unfold n; lia).
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2320 + D), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  pose proof M2S as (M2a & M2b & M2c).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  do 9 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. do 4 lstep.
  call try_init_spec; [assumption| rewrite EU48; exact ST| rewrite EU48; lia| rewrite ?EU48; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false. do 6 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CP3 : chk_ok mm p n)
      by (apply (chk_ok_agree m mm p _ CP ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (CQ3 : chk_ok mm q n)
      by (apply (chk_ok_agree m mm q _ CQ ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (M2S3 : m2s_cells mm) by (split; [| split]; assumption);
    assert (IC3 : icells_cmp mm) by (split; [| split; [| split; [| split; [| split]]]]; assumption)
  end.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply (icmp_common_spec RIP 0x15c4f4 D ltac:(lia) eq_refl D_pos CALLEE) with (lo := lo) (p := p) (q := q) (bp := bp) (bq := bq)
                    | post_call segs mm] end;
    [reflexivity| reflexivity| reflexivity| reflexivity| exact LEN| exact NZ| exact P0| exact Q0| exact PH| exact QH| assumption| assumption
    | rewrite EU48; fold n; lia| rewrite EU48; fold n; lia| exact CP3| exact CQ3| exact M2S3| exact IC3| assumption
    | rewrite EU48; exact ST2| rewrite EU48; lia| unfold kHighShadowEnd; lia| rewrite EU48; lia|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST4 end.
  do 5 lstep.
  release_frame FR ST4 usp.
  lstep.
  unfold cmp_post. sys_finish.
  - rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  - rewrite EU. assumption.
Qed.
End Shellimemcmp.

Section Shellibcmp.
Hypothesis RIP : rip_stmt.
Variable D : Z.
Hypothesis D_pos : 0 <= D.
Hypothesis CALLEE : cmp_fn 0x15c424 D.

Lemma ibcmp_shell_spec : cmp_fn 0x6e5cc (2320 + D).
Proof using RIP D_pos CALLEE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo
    -> -> -> LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bp)) in *.
  assert (N1 : 1 <= n) by (unfold n; lia).
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2320 + D), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  pose proof M2S as (M2a & M2b & M2c).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  do 9 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. do 4 lstep.
  call try_init_spec; [assumption| rewrite EU48; exact ST| rewrite EU48; lia| rewrite ?EU48; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false. do 6 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CP3 : chk_ok mm p n)
      by (apply (chk_ok_agree m mm p _ CP ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (CQ3 : chk_ok mm q n)
      by (apply (chk_ok_agree m mm q _ CQ ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (M2S3 : m2s_cells mm) by (split; [| split]; assumption);
    assert (IC3 : icells_cmp mm) by (split; [| split; [| split; [| split; [| split]]]]; assumption)
  end.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply (icmp_common_spec RIP 0x15c424 D ltac:(lia) eq_refl D_pos CALLEE) with (lo := lo) (p := p) (q := q) (bp := bp) (bq := bq)
                    | post_call segs mm] end;
    [reflexivity| reflexivity| reflexivity| reflexivity| exact LEN| exact NZ| exact P0| exact Q0| exact PH| exact QH| assumption| assumption
    | rewrite EU48; fold n; lia| rewrite EU48; fold n; lia| exact CP3| exact CQ3| exact M2S3| exact IC3| assumption
    | rewrite EU48; exact ST2| rewrite EU48; lia| unfold kHighShadowEnd; lia| rewrite EU48; lia|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST4 end.
  do 5 lstep.
  release_frame FR ST4 usp.
  lstep.
  unfold cmp_post. sys_finish.
  - rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  - rewrite EU. assumption.
Qed.
End Shellibcmp.

Section Top.
Hypothesis RIP : rip_stmt.

Lemma cmp_fn_musl_bcmp : cmp_fn 0x15c424 2320.
Proof using RIP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo
    E0 E1 E2 LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lstep. lstep.
  exact (imemcmp_shell_spec RIP 0 ltac:(lia) cmp_fn_musl ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p q bp bq lo E0 E1 E2 LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH).
Qed.

Notation IBCMP_DEPTH := 4640%Z (only parsing).

Theorem ibcmp_spec : cmp_fn 0x6c42c IBCMP_DEPTH.
Proof using RIP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo
    E0 E1 E2 LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lstep.
  exact (ibcmp_shell_spec RIP 2320 ltac:(lia) cmp_fn_musl_bcmp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p q bp bq lo E0 E1 E2 LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH).
Qed.
End Top.
