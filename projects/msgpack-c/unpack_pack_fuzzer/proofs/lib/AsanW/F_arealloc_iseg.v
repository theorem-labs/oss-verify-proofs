(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AQConst ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2 AKitQ F_aintal. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_memcpy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition AREALLOC_SYM : Z := 0x5e41c.
Definition AREALLOC_PC : Z := 0x5e958.

Definition ricptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk0 junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5e96c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x5e958) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 p) (Z_to_bv 64 0x5e958) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5e9b0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2192, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2120) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xdacc0 (0xdacc0 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).

Lemma ricptA_spec : forall (p n : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2192 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 p -> 0 <= p < 2^47 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  rw_cells asegs m 0xda798 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xda7bc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8); C8 (Z_to_bv 64 0xd72b8); C8 (Z_to_bv 64 0xd9ab8);
                             C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a0)] ->
  rw_cells asegs m 0x16b60a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd14f8 [C8 (Z_to_bv 64 0x169560)] -> rw_cells asegs m 0x169560 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ricptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> PR -> NR INI MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RSTK. atop_facts.
  unfold AREALLOC_SYM, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MU0.
  step.
  carve_frame 2144%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 2144%nat _ [] [8; 16; 2040; 80]%nat) in FR; [| cbn; lia]. cbn [app mk_CB_cells] in FR.
  rw_split FR 1%nat FRp FR1. rw_split FR1 1%nat FRa FR2. rw_split FR2 1%nat FRt FRs.
  do 9 step.
  zstep. zstep. step. step. step.

  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.
  do 4 step. release_frame FR ST (bv_unsigned sp + -2144).
  step. if_lit.

  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs mm (896200 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk asegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk asegs ?mm 896192 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells asegs ?mm 1480008 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at asegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z MU1 WM1.

  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.
  zstep.
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (896200 + 8 * j) with (896192 + j * 8 + 8) in RD by lia.
  step. clear RD.
  step. step. if_lit.
  clear Hj JR.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  step. sstep. step.
  step. step. lstep. step. step.
  step. step. if_lit.
  step. step. step.
  step. step. lstep. step.
  step. step. lstep. step. step.
  step. zstep. zstep. zstep. step.
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.
  step. if_lit.
  zstep. zstep. step. step. step. step.
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold ricptA_post. do 10 eexists. do 3 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRp|]. split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
  intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
  intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End CANSEC1.

Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC2. Context {rc : runConstT}.
Definition ricptB_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n t lo : Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a7 t3 t4 t5 t6 : word) m' sj' (junkR : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x3d734) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3d764) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp - 2144); (t + 2800, t + 3168)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) [C8 s4; C8 s3; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x3d6ec)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 junkR; C8 (Z_to_bv 64 0x5e9c8)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ sj' = upd (upd sj 7%nat (Z_to_bv 64 (bv_unsigned (nth 7%nat sj w0) + 1))) 8%nat (Z_to_bv 64 (bv_unsigned (nth 8%nat sj w0) + n)).

Lemma ricptB_spec : forall RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n ctx t lo : Z) (sj : list word),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2240 ->
  mem_inv asegs m ->
  0 < p < 2^64 -> 0 < n < 2^64 ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m 0xd9320 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xd9324 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (ricptB_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n t lo sj m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e9b4) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros ST CEIL LO MI PR NR TP TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ RIMG RSTK RCTX RT. atop_facts.
  pose proof T0 as T0L. unfold iclr, AIMG_LO, AIMG_HI in T0L.
  word_range sp SPR. unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp - 2144); (t + 2800, t + 3168)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step. step.
  carve_frame 16%nat ST. rename FR into FRR.
  do 4 step.
  step. if_cases K0; zify_cond K0; [exfalso; clear - K0 PR; lia|].
  step.
  step. if_cases K1; zify_cond K1; [| exfalso; clear - K1 NR; lia].
  do 5 step.
  carve_frame 48%nat ST.
  do 7 step.
  step. if_cases K2; zify_cond K2; [exfalso; clear - K2 PR; lia|].
  step.
  step. if_cases K3; zify_cond K3; [exfalso; clear - K3 NR; lia|].
  step. step. step.
  step. call_sp (thread_stats_spec RNG ctx t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- rng _ _ _ => solve_rng
       | |- _ => lia
       end.
  rename POST into ST.
  aload STATS 7 (t + 2800 + 56).
  aload STATS 8 (t + 2800 + 64).
  zstep. zstep.
  astore STATS 7.
  astore STATS 8.
  do 6 step.
  apply evtF_done. unfold ricptB_post, AINSTANCE. do 11 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FR|]. split; [exact FRR|]. split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ| reflexivity].
Qed.
End CANSEC2.

Section CANSEC3. Context {rc : runConstT}.
Definition ricptC_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (hm n nold UB : Z) (src : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x3d7e0) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (hm + 16))
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1)
                  a6 a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (Z.min n nold)) (Z_to_bv 64 UB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3d7f8) fc None m' (seg_rom asegs)
    /\ munch [(UB, UB + Z.min n nold)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' UB [CB (Z.to_nat (Z.min n nold)) src]
    /\ bytes_at asegs m' (hm + 16) src.

Lemma ricptC_spec : forall RNG ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (hm n nold UB b1 actx : Z) (src junk : list byte),
  mem_inv asegs m ->
  0 < UB < 2^64 -> 0 < n < 2^64 -> 0 <= nold < 2^32 -> 0 <= hm -> hm + 16 + nold < 2^64 -> 0 <= b1 < 256 ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 nold); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m 0xd1540 [C8 (Z_to_bv 64 0xd3420)] ->
  rw_cells asegs m 0xd3420 [C8 (Z_to_bv 64 0xc74a0); C8 (Z_to_bv 64 0xc78a4)] ->
  bytes_at asegs m (hm + 16) src -> length src = Z.to_nat (Z.min n nold) ->
  rw_cells asegs m UB [CB (Z.to_nat (Z.min n nold)) junk] ->
  (hm + 16 + Z.min n nold <= UB \/ UB + Z.min n nold <= hm + 16) ->
  rng_aimg RNG -> rng RNG hm 16 -> rng RNG (hm + 16) (Z.min n nold) -> rng RNG UB (Z.min n nold) ->
  evtF asegs RNG (ricptC_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc hm n nold UB src m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
             (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (hm + 16))
             (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d768) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI UBR NR NOR HM0 HMB B1 HD GOT REAL SRC LEN DST SEP RIMG RH RS RD.
  word_range sp SPR. unfold AINSTANCE in *.
  pose proof (munch_refl [(UB, UB + Z.min n nold)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.
  step. if_cases K0; zify_cond K0; [exfalso; clear - K0 UBR; lia|].
  replace (hm + 16 + -16) with hm by lia.
  step.
  step. step. step. if_lit.
  step. lstep. step.
  step. if_lit.
  step. step.
  rewrite (zx16_lit 0) by lia. rewrite (zx32_lit nold) by lia.
  zstep. zstep.
  rewrite ?Z.shiftl_0_l, ?Z.mod_0_l, ?Z.lor_0_l by lia.
  step. if_cases K1; zify_cond K1.
  -
    replace (Z.min n nold) with n in * by lia.
    step. step. step.
    step.
    assert (E1 : bv_unsigned (Z_to_bv 64 (hm + 16)) = hm + 16) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    assert (EUB : bv_unsigned (Z_to_bv 64 UB) = UB) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    call memcpy_spec; rewrite ?E1, ?EUB, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI | try assumption ..].
    rewrite ?E1, ?EUB, ?EN in *.
    do 6 step.
    apply evtF_done. unfold ricptC_post, AINSTANCE. replace (Z.min n nold) with n by lia. do 10 eexists.
    split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  -
    replace (Z.min n nold) with nold in * by lia.
    step.
    step. step. step.
    step.
    assert (E1 : bv_unsigned (Z_to_bv 64 (hm + 16)) = hm + 16) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    assert (EUB : bv_unsigned (Z_to_bv 64 UB) = UB) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    assert (EN : bv_unsigned (Z_to_bv 64 nold) = nold) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    call memcpy_spec; rewrite ?E1, ?EUB, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI | try assumption ..].
    rewrite ?E1, ?EUB, ?EN in *.
    do 6 step.
    apply evtF_done. unfold ricptC_post, AINSTANCE. replace (Z.min n nold) with nold by lia. do 10 eexists.
    split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.
End CANSEC3.

Section CANSEC4. Context {rc : runConstT}.
Lemma ricptE_spec : forall RNG ra0 sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v spv s4r s3r s2r s1r s0r : word) (F : bvmap 5 word) fc (m : amem) (lo UB : Z) (junk2 junkR : list byte),
  stk asegs m lo (bv_unsigned sp + -2208) -> ATOP <= lo -> lo <= bv_unsigned sp - 2208 ->
  mem_inv asegs m ->
  0 < UB < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2208) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x3d6ec)] ->
  rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 junkR; C8 (Z_to_bv 64 0x5e9c8)] ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2144) csA /\ cells_size csA = 8%nat) ->
  (exists csS, rw_cells asegs m (bv_unsigned sp + -2136) csS /\ cells_size csS = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 spv; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6',
      ms' = MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m (seg_rom asegs)
      /\ a0' = Z_to_bv 64 UB
      /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x (Z_to_bv 64 UB) s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d7fc) fc None m (seg_rom asegs)).
Proof.
  intros until junkR. intros ST CEIL LO MI UBR FRR FRa [csA [FRA SZA]] [csS [FRS SZS]] [csT [FRT SZT]] FRI RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. do 6 step. zstep. step.
  step. if_cases K0; zify_cond K0; [exfalso; clear - K0 UBR; lia|].
  step. zstep. step.
  zstep. do 8 step. zstep. step.
  release_frame FRR ST (bv_unsigned sp + -2160).
  release_frame FRa ST (bv_unsigned sp + -2144).
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2136).
  pose proof (rw_cells_forget asegs _ _ _ FRS) as [jS FRS']. rewrite SZS in FRS'. clear FRS.
  release_frame FRS' ST (bv_unsigned sp + -2120).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRI ST (bv_unsigned sp).
  apply evtF_done. do 15 eexists. split; [reflexivity|]. split; [reflexivity | exact ST].
Qed.
End CANSEC4.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AQConst.TwinB ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB AKitQ.TwinB F_aintal.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3. Import F_memcpy.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition AREALLOC_SYM : Z := 0x5edac.
Definition AREALLOC_PC : Z := 0x5f2e8.

Definition ricptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk0 junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5f2fc) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x5f2e8) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 p) (Z_to_bv 64 0x5f2e8) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5f340) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2192, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2120) [CB 2040 junk1]
    /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xdce80 (0xdce80 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).

Lemma ricptA_spec : forall (p n : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2192 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 p -> 0 <= p < 2^47 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  rw_cells bsegs m 0xdc958 [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xdc97c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8); C8 (Z_to_bv 64 0xd9478); C8 (Z_to_bv 64 0xdbc78);
                             C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc960)] ->
  rw_cells bsegs m 0x16d7ca [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd3610 [C8 (Z_to_bv 64 0x16b720)] -> rw_cells bsegs m 0x16b720 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (ricptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> PR -> NR INI MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RSTK. atop_facts.
  unfold AREALLOC_SYM, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MU0.
  step.
  carve_frame 2144%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 2144%nat _ [] [8; 16; 2040; 80]%nat) in FR; [| cbn; lia]. cbn [app mk_CB_cells] in FR.
  rw_split FR 1%nat FRp FR1. rw_split FR1 1%nat FRa FR2. rw_split FR2 1%nat FRt FRs.
  do 9 step.
  zstep. zstep. step. step. step.

  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.
  do 4 step. release_frame FR ST (bv_unsigned sp + -2144).
  step. if_lit.

  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs mm (904840 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk bsegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk bsegs ?mm 904832 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells bsegs ?mm 1488648 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at bsegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z MU1 WM1.

  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.
  zstep.
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (904840 + 8 * j) with (904832 + j * 8 + 8) in RD by lia.
  step. clear RD.
  step. step. if_lit.
  clear Hj JR.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  step. sstep. step.
  step. step. lstep. step. step.
  step. step. if_lit.
  step. step. step.
  step. step. lstep. step.
  step. step. lstep. step. step.
  step. zstep. zstep. zstep. step.
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.
  step. if_lit.
  zstep. zstep. step. step. step. step.
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold ricptA_post. do 10 eexists. do 3 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRp|]. split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
  intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
  intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End CANSEC1.

Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC2. Context {rc : runConstT}.
Definition ricptB_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n t lo : Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a7 t3 t4 t5 t6 : word) m' sj' (junkR : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x3e0c4) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3e0f4) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp - 2144); (t + 2800, t + 3168)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2208)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2208) [C8 s4; C8 s3; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x3e07c)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2160) [CB 8 junkR; C8 (Z_to_bv 64 0x5f358)]
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ sj' = upd (upd sj 7%nat (Z_to_bv 64 (bv_unsigned (nth 7%nat sj w0) + 1))) 8%nat (Z_to_bv 64 (bv_unsigned (nth 8%nat sj w0) + n)).

Lemma ricptB_spec : forall RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n ctx t lo : Z) (sj : list word),
  stk bsegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2240 ->
  mem_inv bsegs m ->
  0 < p < 2^64 -> 0 < n < 2^64 ->
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m 0xdb4e0 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xdb4e4 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (ricptB_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n t lo sj m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5f344) fc None m (seg_rom bsegs)).
Proof.
  intros until sj. intros ST CEIL LO MI PR NR TP TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ RIMG RSTK RCTX RT. atop_facts.
  pose proof T0 as T0L. unfold iclr, AIMG_LO, AIMG_HI in T0L.
  word_range sp SPR. unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp - 2144); (t + 2800, t + 3168)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. step. step. step.
  carve_frame 16%nat ST. rename FR into FRR.
  do 4 step.
  step. if_cases K0; zify_cond K0; [exfalso; clear - K0 PR; lia|].
  step.
  step. if_cases K1; zify_cond K1; [| exfalso; clear - K1 NR; lia].
  do 5 step.
  carve_frame 48%nat ST.
  do 7 step.
  step. if_cases K2; zify_cond K2; [exfalso; clear - K2 PR; lia|].
  step.
  step. if_cases K3; zify_cond K3; [exfalso; clear - K3 NR; lia|].
  step. step. step.
  step. call_sp (thread_stats_spec RNG ctx t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- rng _ _ _ => solve_rng
       | |- _ => lia
       end.
  rename POST into ST.
  aload STATS 7 (t + 2800 + 56).
  aload STATS 8 (t + 2800 + 64).
  zstep. zstep.
  astore STATS 7.
  astore STATS 8.
  do 6 step.
  apply evtF_done. unfold ricptB_post, AINSTANCE. do 11 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FR|]. split; [exact FRR|]. split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ| reflexivity].
Qed.
End CANSEC2.

Section CANSEC3. Context {rc : runConstT}.
Definition ricptC_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (hm n nold UB : Z) (src : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x3e170) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (hm + 16))
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1)
                  a6 a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (Z.min n nold)) (Z_to_bv 64 UB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3e188) fc None m' (seg_rom bsegs)
    /\ munch [(UB, UB + Z.min n nold)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' UB [CB (Z.to_nat (Z.min n nold)) src]
    /\ bytes_at bsegs m' (hm + 16) src.

Lemma ricptC_spec : forall RNG ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (hm n nold UB b1 actx : Z) (src junk : list byte),
  mem_inv bsegs m ->
  0 < UB < 2^64 -> 0 < n < 2^64 -> 0 <= nold < 2^32 -> 0 <= hm -> hm + 16 + nold < 2^64 -> 0 <= b1 < 256 ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 nold); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m 0xd3658 [C8 (Z_to_bv 64 0xd5538)] ->
  rw_cells bsegs m 0xd5538 [C8 (Z_to_bv 64 0xc95bc); C8 (Z_to_bv 64 0xc99c0)] ->
  bytes_at bsegs m (hm + 16) src -> length src = Z.to_nat (Z.min n nold) ->
  rw_cells bsegs m UB [CB (Z.to_nat (Z.min n nold)) junk] ->
  (hm + 16 + Z.min n nold <= UB \/ UB + Z.min n nold <= hm + 16) ->
  rng_aimg RNG -> rng RNG hm 16 -> rng RNG (hm + 16) (Z.min n nold) -> rng RNG UB (Z.min n nold) ->
  evtF bsegs RNG (ricptC_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc hm n nold UB src m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
             (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (hm + 16))
             (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e0f8) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI UBR NR NOR HM0 HMB B1 HD GOT REAL SRC LEN DST SEP RIMG RH RS RD.
  word_range sp SPR. unfold AINSTANCE in *.
  pose proof (munch_refl [(UB, UB + Z.min n nold)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step.
  step. if_cases K0; zify_cond K0; [exfalso; clear - K0 UBR; lia|].
  replace (hm + 16 + -16) with hm by lia.
  step.
  step. step. step. if_lit.
  step. lstep. step.
  step. if_lit.
  step. step.
  rewrite (zx16_lit 0) by lia. rewrite (zx32_lit nold) by lia.
  zstep. zstep.
  rewrite ?Z.shiftl_0_l, ?Z.mod_0_l, ?Z.lor_0_l by lia.
  step. if_cases K1; zify_cond K1.
  -
    replace (Z.min n nold) with n in * by lia.
    step. step. step.
    step.
    assert (E1 : bv_unsigned (Z_to_bv 64 (hm + 16)) = hm + 16) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    assert (EUB : bv_unsigned (Z_to_bv 64 UB) = UB) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    call memcpy_spec; rewrite ?E1, ?EUB, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI | try assumption ..].
    rewrite ?E1, ?EUB, ?EN in *.
    do 6 step.
    apply evtF_done. unfold ricptC_post, AINSTANCE. replace (Z.min n nold) with n by lia. do 10 eexists.
    split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  -
    replace (Z.min n nold) with nold in * by lia.
    step.
    step. step. step.
    step.
    assert (E1 : bv_unsigned (Z_to_bv 64 (hm + 16)) = hm + 16) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    assert (EUB : bv_unsigned (Z_to_bv 64 UB) = UB) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    assert (EN : bv_unsigned (Z_to_bv 64 nold) = nold) by (apply Z_to_bv_small; unfold bv_modulus; lia).
    call memcpy_spec; rewrite ?E1, ?EUB, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI | try assumption ..].
    rewrite ?E1, ?EUB, ?EN in *.
    do 6 step.
    apply evtF_done. unfold ricptC_post, AINSTANCE. replace (Z.min n nold) with nold by lia. do 10 eexists.
    split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.
End CANSEC3.

Section CANSEC4. Context {rc : runConstT}.
Lemma ricptE_spec : forall RNG ra0 sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v spv s4r s3r s2r s1r s0r : word) (F : bvmap 5 word) fc (m : amem) (lo UB : Z) (junk2 junkR : list byte),
  stk bsegs m lo (bv_unsigned sp + -2208) -> ATOP <= lo -> lo <= bv_unsigned sp - 2208 ->
  mem_inv bsegs m ->
  0 < UB < 2^64 ->
  rw_cells bsegs m (bv_unsigned sp + -2208) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x3e07c)] ->
  rw_cells bsegs m (bv_unsigned sp + -2160) [CB 8 junkR; C8 (Z_to_bv 64 0x5f358)] ->
  (exists csA, rw_cells bsegs m (bv_unsigned sp + -2144) csA /\ cells_size csA = 8%nat) ->
  (exists csS, rw_cells bsegs m (bv_unsigned sp + -2136) csS /\ cells_size csS = 16%nat) ->
  (exists csT, rw_cells bsegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells bsegs m (bv_unsigned sp + -80) [C8 spv; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6',
      ms' = MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m (seg_rom bsegs)
      /\ a0' = Z_to_bv 64 UB
      /\ stk bsegs m lo (bv_unsigned sp))
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x (Z_to_bv 64 UB) s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e18c) fc None m (seg_rom bsegs)).
Proof.
  intros until junkR. intros ST CEIL LO MI UBR FRR FRa [csA [FRA SZA]] [csS [FRS SZS]] [csT [FRT SZT]] FRI RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. do 6 step. zstep. step.
  step. if_cases K0; zify_cond K0; [exfalso; clear - K0 UBR; lia|].
  step. zstep. step.
  zstep. do 8 step. zstep. step.
  release_frame FRR ST (bv_unsigned sp + -2160).
  release_frame FRa ST (bv_unsigned sp + -2144).
  pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2136).
  pose proof (rw_cells_forget bsegs _ _ _ FRS) as [jS FRS']. rewrite SZS in FRS'. clear FRS.
  release_frame FRS' ST (bv_unsigned sp + -2120).
  pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRI ST (bv_unsigned sp).
  apply evtF_done. do 15 eexists. split; [reflexivity|]. split; [reflexivity | exact ST].
Qed.
End CANSEC4.
End TwinB.
