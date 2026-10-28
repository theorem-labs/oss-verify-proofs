(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 ABytes AModelFacts APrimFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma cb_take : forall m A n k bs,
  rw_cells bsegs m A [CB (Z.to_nat n) bs] -> 0 <= k <= n ->
  rw_cells bsegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)] /\ rw_cells bsegs m (A + k) [CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)].
Proof.
  intros m A n k bs H HK.
  assert (L : length bs = Z.to_nat n) by (destruct H as [[[WF _] _] _]; cbn in WF; exact WF).
  assert (H2 : rw_cells bsegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs); CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)]).
  { eapply rw_cells_recast; [exact H | | |].
    - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
    - cbn [cells_size csize]. lia. }
  lazymatch type of H2 with rw_cells _ _ _ [?x; ?y] => change [x; y] with ([x] ++ [y]) in H2 end.
  apply rw_cells_app in H2. destruct H2 as [HA HR]. cbn [cells_size csize] in HR. rewrite Nat.add_0_r, Z2Nat.id in HR by lia.
  split; [exact HA | exact HR].
Qed.

(* [comment removed for export] *)
Lemma cb_app2 : forall m A n1 bs1 n2 bs2,
  rw_cells bsegs m A [CB n1 bs1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells bsegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros m A n1 bs1 n2 bs2 H1 H2.
  assert (H : rw_cells bsegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  cbn [app] in H. eapply rw_cells_recast; [exact H | | |].
  - destruct H1 as [[[W1 _] _] _]. destruct H2 as [[[W2 _] _] _]. cbn in W1, W2 |- *. rewrite length_app. repeat split; lia.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn [cells_size csize]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stats_class_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (X size : Z),
  a0 = Z_to_bv 64 X -> 0 <= X -> X + 112 < 2^64 ->
  24 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 112)) (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34198) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x340a4) fc None m (seg_rom bsegs)).
Proof.
  intros until size. intros -> X0 X1 SZ M8 RIMG.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
  step. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
  - eapply evtF_mono; [eapply (classblock2_spec RNG); [lia | exact M8 | exact RIMG] |].
    cbv beta. intros ms' P. destruct P as (a2' & a3' & a4' & a5' & a6' & ->). do 5 eexists. reflexivity.
  - zstep. zstep. rewrite <- (CSM ltac:(lia)). step.            (* [comment removed for export] *)
    apply evtF_done. do 5 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fill_len_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min n 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x341d0) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x341c4) fc None m (seg_rom bsegs)).
Proof.
  intros until n. intros N RIMG.
  step. step. if_cases K; zify_cond K.                           (* [comment removed for export] *)
  - replace (Z.min n 4096) with n by lia. apply evtF_done. reflexivity.
  - step. replace (Z.min n 4096) with 4096 by lia. apply evtF_done. reflexivity.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Definition allocD_postG (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ (16 < rz_size n -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).

Lemma allocD_gen : forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
    (n t c AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
    (fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6 : word),
  stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + n <= ATOP -> AB mod 16 = 0 ->
  class_id (needed_size n) = c ->
  (t + 4096 <= AB \/ AB + 65536 <= t) ->
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m 0xcf560 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xcf564 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
  rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
  0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcd524 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0xc72f8 [C8 (Z_to_bv 64 0x161828); C8 (Z_to_bv 64 0xcd4f8); C8 (Z_to_bv 64 0xcfcf8);
                             C8 (Z_to_bv 64 0xd09e8); C8 (Z_to_bv 64 0xd09f0); C8 (Z_to_bv 64 0xd09e0)] ->
  rw_cells bsegs m 0xc7328 [C8 (Z_to_bv 64 0xc91b8)] ->
  rw_cells bsegs m 0xc91b0 [C8 (Z_to_bv 64 0xc0638); C8 (Z_to_bv 64 0xc0a3c)] ->
  rw_cells bsegs m 0xc7f60 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x602cc0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x1617c0 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 <= b1m < 256 -> 0 < id < 2^31 ->
  (16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
  evtF bsegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x34054) fc None m (seg_rom bsegs)).
Proof.
  intros until t6.
  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  step. call_sp (thread_stats_spec RNG (al_ctx L) t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  rename POST into ST.
  aload STATS 2 (t + 2800 + 16).                                 (* [comment removed for export] *)
  aload STATS 0 (t + 2800 + 0).                                  (* [comment removed for export] *)
  aload STATS 1 (t + 2800 + 8).                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep. zstep. zstep.                       (* [comment removed for export] *)
  astore STATS 0.                                                (* [comment removed for export] *)
  astore STATS 1.                                                (* [comment removed for export] *)
  astore STATS 2.                                                (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2: { exfalso. lia. }          (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evtF_cut; [eapply (stats_class_spec RNG); [reflexivity | lia | lia | lia | clear -NS RSM RZM; rewrite NS; Z.div_mod_to_equations; lia | exact RIMG] |].
  cbv beta. intros msS PS. destruct PS as (a2s & a3s & a4s & a5s & a6s & ->). rewrite HC.
  zstep. zstep.                                                  (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 c 3) by lia. change (2^3) with 8.
  aload STATS (14 + c) (t + 2912 + c * 8).                       (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  astore STATS (14 + c).                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  carry UJ MUs WMs ltac:(with_box DJT lia). carry HDR MUs WMs ltac:(with_box DJT lia).
  unbox LH.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH' : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH RZ). box LH. carry LH MUs WMs ltac:(with_box DJT lia). exact LH. }
  clear LH MUs WMs. box LH'. box STATS.
  snapshot [(UB - 16, UB + n); (AB, AB + 16); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUc WMc.
  snapshot [(UB - 16, UB + n); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUl WMl.
  (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. lstep. step. if_lit.                               (* [comment removed for export] *)
  eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG] |]. cbv beta. intros msF ->.   (* [comment removed for export] *)
  set (fl := Z.min n 4096) in *.
  destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
  step. step. step. lstep. step.                                 (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => exact UJ1
       | |- rng _ _ _ => eapply rng_sub'; [exact RU|]; subst fl; lia
       | |- _ => subst fl; atop_facts; lia
       end.
  rename POST into UF1.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (UF : rw_cells bsegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
  { replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
    apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
  clear UF1 UJ2.
  (* [comment removed for export] *)
  step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
  lstep. zstep. zstep. zstep. zstep. step.                       (* [comment removed for export] *)
  sstep. step. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  unbox LH'.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH' RZ). box LH'. carry LH' MUl WMl ltac:(lia). exact LH'. }
  clear LH' MUl WMl.
  pose proof (rz_size_cases n) as RZC. box RZC.
  step. if_cases K3; zify_cond K3.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    clear LH.
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ _ _ => exact HK
         | |- rng _ _ _ => solve_rng
         | |- _ => atop_facts; lia
         end.
    rename POST into ST.
    do 16 step.                                                  (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    carry STATS MUc WMc ltac:(with_box DJT lia).
    apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
    intros RZ. exfalso. lia.
  - (* [comment removed for export] *)
    specialize (LH ltac:(with_box RZC lia)).
    zstep. step. if_cases K4; zify_cond K4. { exfalso. with_box RZC lia. }   (* [comment removed for export] *)
    step. step.                                                  (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ _ _ => exact HK
         | |- rng _ _ _ => solve_rng
         | |- _ => atop_facts; lia
         end.
    rename POST into ST.
    do 16 step.
    release_frame FR ST (bv_unsigned sp).
    carry STATS MUc WMc ltac:(with_box DJT lia).
    apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
    intros _. exact LH.
Qed.
End CANSEC2.
(* [comment removed for export] *)
