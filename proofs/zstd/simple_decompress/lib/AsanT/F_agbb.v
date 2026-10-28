(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AKit AKit2 AKitQ.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition gbb_entry := 0x35dd8.
End CANSEC1.
Abbreviation GBB_STACK := 32.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition nb_step (p acc ch : Z) : Z :=
  if p <? ch then acc else if p - ch <? p - acc then ch else acc.
Definition nb_fold (p acc : Z) (l : list Z) : Z := fold_left (nb_step p) l acc.

Lemma nb_fold_cons : forall p acc ch l, nb_fold p acc (ch :: l) = nb_fold p (nb_step p acc ch) l.
Proof. reflexivity. Qed.

Lemma nb_step_range : forall p acc ch, 0 <= acc <= p -> 0 <= ch -> 0 <= nb_step p acc ch <= p.
Proof. intros p acc ch H Hc. unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - acc)); lia. Qed.

(* [comment removed for export] *)
Lemma nb_fold_finds : forall p mb l acc,
  0 <= acc <= mb -> mb <= p -> Forall (fun ch => 0 <= ch /\ (ch <= p -> ch <= mb)) l ->
  (In mb l \/ acc = mb) -> nb_fold p acc l = mb.
Proof.
  intros p mb l. induction l as [|ch l IH]; intros acc HA HM HL HIN.
  - cbn. destruct HIN as [[]| ->]; reflexivity.
  - rewrite nb_fold_cons. apply Forall_cons_iff in HL. destruct HL as [[C0 C1] HL].
    apply IH; [| exact HM | exact HL |].
    + unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - acc)); [| lia]. split; [lia|]. apply C1. lia.
    + destruct HIN as [[E | HIN] | ->].
      * right. subst ch. unfold nb_step. destruct (Z.ltb_spec p mb); [lia|]. destruct (Z.ltb_spec (p - mb) (p - acc)); lia.
      * left; exact HIN.
      * right. unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - mb)); [| lia].
        specialize (C1 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gbb_loop_spec : forall RNG (d : nat) (i n PA p acc : Z) (bases : list Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> Z.of_nat (length bases) = n ->
  u64arr bsegs m PA (map (Z_to_bv 64) bases) ->
  Forall (fun ch => 0 <= ch < 2^64) bases -> 0 <= acc <= p -> p < 2^64 ->
  0 <= PA -> PA + 8 * n < 2^47 ->
  rng RNG PA (8 * n) ->
  evtF bsegs RNG (fun ms' => exists a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 (Z_to_bv 64 p) (Z_to_bv 64 (PA + 8 * n))
                    (Z_to_bv 64 (nb_fold p acc (skipn (Z.to_nat i) bases))) (Z_to_bv 64 (PA + 8 * n)) a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35e70) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 p) (Z_to_bv 64 (PA + 8 * i)) (Z_to_bv 64 acc) (Z_to_bv 64 (PA + 8 * n)) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35e44) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LEN ARR BR ACC P64 PA0 PA1 RPA; [lia|].
  destruct (nth_error bases (Z.to_nat i)) as [ch|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) BR ch (nth_error_In _ _ NTH)) as CHR. cbv beta in CHR.
  assert (NTHm : nth_error (map (Z_to_bv 64) bases) (Z.to_nat i) = Some (Z_to_bv 64 ch)) by (rewrite nth_error_map, NTH; reflexivity).
  pose proof (u64arr_read bsegs _ _ _ i (Z_to_bv 64 ch) (wa (PA + 8 * i)) ARR NTHm ltac:(lia) eq_refl) as RD.
  pose proof (rng_sub _ _ _ (PA + 8 * i) 8 RPA ltac:(lia) ltac:(lia)) as RDi.
  (* [comment removed for export] *)
  assert (SK : skipn (Z.to_nat i) bases = ch :: skipn (Z.to_nat (i + 1)) bases).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. clear -NTH.
    revert NTH. generalize (Z.to_nat i) as k. clear. intros k. revert bases.
    induction k as [|k IHk]; intros [|b bs] H; cbn in *; try discriminate; [injection H as ->; reflexivity| apply IHk; exact H]. }
  rewrite SK, nb_fold_cons.
  step. clear RD RDi.                                          (* [comment removed for export] *)
  zstep. zstep. step.                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  step; if_cases K; zify_cond K;
    [ step; if_cases K'; zify_cond K'; [ | step; step ]
    | step; step; if_cases K'; zify_cond K'; [ | step; step; step ] ].
  all: setreg 13 (Z_to_bv 64 (nb_step p acc ch))
         ltac:(unfold nb_step; rewrite ?Z.mod_small in K by lia;
               destruct (Z.ltb_spec p ch); destruct (Z.ltb_spec (p - ch) (p - acc)); first [reflexivity | exfalso; lia]).
  all: zstep; setreg 12 (Z_to_bv 64 (PA + 8 * (i + 1))) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  all: pose proof (nb_step_range p acc ch ACC ltac:(lia)) as ACC'.
  all: step; if_cases KE; zify_cond KE.                        (* [comment removed for export] *)
  all: try (rewrite ?unsigned_lit in KE by lia).
  1,3,5,7: (* [comment removed for export] *)
       assert (EI : i + 1 = n) by lia;
       apply evtF_done; do 4 eexists;
       rewrite skipn_all2 by (rewrite <- EI in *; lia); cbn [nb_fold fold_left]; rewrite EI; reflexivity.
  all: eapply evtF_mono; [eapply (IH (i + 1) n PA p (nb_step p acc ch) bases); try eassumption; try lia |].
  all: cbv beta; intros ms' (a5' & a6' & a7' & t0' & ->); do 4 eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gbb_mtx_to_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells bsegs m 0xcc940 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xcc940 [C4 (Z_to_bv 64 b)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 1 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.
Lemma gbb_mtx_of_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells bsegs m 0xcc940 [C4 (Z_to_bv 64 b)] ->
  rw_cells bsegs m 0xcc940 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 2 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.

Definition gbb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mb + 4096)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - GBB_STACK, bv_unsigned sp); (0xcc940, 0xcc944)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Lemma sec_gbb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p PA nres nsec mb ms lo : Z) (bases : list Z) (h2 h3 : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - GBB_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 0xcc6d8 -> a1 = Z_to_bv 64 p ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcc6d8 [C8 (Z_to_bv 64 4096)] -> rw_cells bsegs m 0xcc6e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells bsegs m 0xcc708 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  u64arr bsegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec -> 1 <= nsec ->
  ablk PA (PA + 8 * nsec) -> PA + 8 * nsec <= ATOP ->       (* [comment removed for export] *)
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= p -> ch <= mb)) bases -> In mb bases ->
  rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 h2; C8 h3] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> mb <= p < mb + ms -> 32 <= ms -> mb + ms <= ATOP ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG PA (8 * nsec) -> rng RNG mb 32 ->
  evtF bsegs RNG (gbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gbb_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until h3. intros ST CEIL LO MI -> -> I64 I72 NSC MTX ARR LEN N1 PA0b PA1 BR IN HDR MAL MPOSb PIN MS32 MCE RA RIMG RSTK RPA RMB.
  pose proof (ablk_lin _ _ PA0b) as PA0. pose proof (ablk_lin _ _ MPOSb) as MPOS. unfold AIMG_HI in PA0, MPOS.   (* [comment removed for export] *)
  unfold gbb_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - GBB_STACK, bv_unsigned sp); (0xcc940, 0xcc944)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  box ARR. box HDR.
  carve_frame 32%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. zstep. step.                                           (* [comment removed for export] *)
  apply (gbb_mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 837952) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0. { exfalso. clear -K0 N1 LEN PA1 PA0. rewrite ?unsigned_lit in K0 by lia. lia. }   (* [comment removed for export] *)
  step. step. zstep. zstep.                                    (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -N1 PA0 PA1; lia).
  step.                                                        (* [comment removed for export] *)
  carry ARR MU WM ltac:(rewrite length_map; clear -SPR CEIL LO PA0 PA1 LEN; lia).
  replace (Z_to_bv 64 PA : word) with (Z_to_bv 64 (PA + 8 * 0) : word) by (f_equal; clear; lia).
  eapply evtF_cut.
  { eapply (gbb_loop_spec RNG (Z.to_nat (nsec - 0)) 0 nsec PA p 0 bases); try eassumption; try (clear -N1 LEN PA0 PA1 PIN MPOS MCE; lia).
    eapply Forall_impl; [| exact BR]. cbn. intros ch [H _]. exact H. }
  cbv beta. intros ms' (a5' & a6' & a7' & t0' & ->). change (skipn (Z.to_nat 0) bases) with bases.
  rewrite (nb_fold_finds p mb bases 0); [| clear -MPOS; lia | clear -PIN; lia | | left; exact IN].
  2: { eapply Forall_impl; [| exact BR]. cbn. intros ch [H1 H2]. split; [clear -H1; lia| exact H2]. }
  (* [comment removed for export] *)
  carry HDR MU WM ltac:(clear -SPR CEIL LO MPOS MCE PIN MS32; lia).
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 MPOS MCE PIN. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2 MPOS MCE PIN. rewrite ?unsigned_lit in K2 by lia. lia. }   (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 MPOS MCE PIN. rewrite ?unsigned_lit in K3 by lia. lia. }   (* [comment removed for export] *)
  step. if_cases K4; zify_cond K4. { exfalso. clear -K4 MPOS MCE PIN. rewrite ?unsigned_lit in K4 by lia. lia. }   (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. clear -K5 MPOS MCE PIN. rewrite ?unsigned_lit in K5 by lia. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; change 4095 with (2^12 - 1); rewrite zb_land_mask_l by (clear; lia); change (2^12) with 4096; clear -MAL; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (mb + 4096)) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply (gbb_mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  step.                                                        (* [comment removed for export] *)
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  apply evtF_done. unfold gbb_post. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. exact MTX.
Qed.
End CANSEC2.
