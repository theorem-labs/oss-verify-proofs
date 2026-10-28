(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma asan_inited_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells bsegs m 0xd09d8 [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5ac74) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros INI RIMG.
  do 6 step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_current_thread_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (ctx t lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m 0xcf560 [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xcf564 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] ->
  rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 ->
  evtF bsegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e384) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> TI TK T88 TSD CT C0 C1 RIMG RSTK RCTX.
  unfold ATP, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  do 3 step.            (* [comment removed for export] *)
  do 4 step. if_false.  (* [comment removed for export] *)
  lstep. step.          (* [comment removed for export] *)
  do 7 lstep.           (* [comment removed for export] *)
  step. if_cases K; zify_cond K; [exfalso; lia|]. step.   (* [comment removed for export] *)
  do 3 step.            (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stack_top_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t top bot : Z),
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 t ->
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> 0 <= t -> t + 4096 <= ATOP ->
  rng RNG t 4096 ->
  evtF bsegs RNG (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 top) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e548) fc None m (seg_rom bsegs)).
Proof.
  intros until bot. intros MI -> TB SW B0 BT TT T0 TC RT. atop_facts.
  lstep. step. step. if_lit.  (* [comment removed for export] *)
  do 2 step.                  (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  rewrite (sel_mask_true (bot <? top) top) by (first [apply Z.ltb_lt; lia | lia]).
  step. apply evtF_done. eexists. reflexivity.
Qed.

Lemma stack_bottom_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t top bot : Z),
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 t ->
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> 0 <= t -> t + 4096 <= ATOP ->
  rng RNG t 4096 ->
  evtF bsegs RNG (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 bot) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e5a0) fc None m (seg_rom bsegs)).
Proof.
  intros until bot. intros MI -> TB SW B0 BT TT T0 TC RT. atop_facts.
  lstep. step. step. if_lit.  (* [comment removed for export] *)
  do 2 step.                  (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  rewrite (sel_mask_true (bot <? top) bot) by (first [apply Z.ltb_lt; lia | lia]).
  step. apply evtF_done. eexists. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma uchain_invalid_nil : forall m top pc p f k tr,
  uchain m top pc p f k tr -> ~ (p < f /\ f < top - 16 /\ f mod 8 = 0 /\ (0 < k)%nat) -> tr = [].
Proof. intros m top pc p f k tr H Hn. destruct H; [reflexivity| exfalso; apply Hn; auto | exfalso; apply Hn; auto]. Qed.

(* [comment removed for export] *)
Definition uwf_post (S pc top spf : Z) (raf s0f s1f s2f s3f s4f s5f s6f : word)
    (gp tp t0 t1 t2 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (size : nat) (tb : list word) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a2' a5' a6' a7' m' tb',
    ms' = MS (mkR raf (Z_to_bv 64 (spf + 64)) gp tp t0 t1 t2 s0f s1f
                  (Z_to_bv 64 S) (Z_to_bv 64 pc) a2' (Z_to_bv 64 4096) (Z_to_bv 64 (S + 16)) a5' a6' a7'
                  s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc raf) fc None m' (seg_rom bsegs)
    /\ munch [(S + 8, S + 12); (S + 16, S + 2056)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (S + 8) [C4 (Z_to_bv 64 (Z.of_nat size + Z.of_nat (length tr)))]
    /\ u64arr bsegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ (forall i, (i < size)%nat -> nth_error tb' i = nth_error tb i)
    /\ map bv_unsigned (firstn (length tr) (skipn size tb')) = tr.

End CANSEC1.
Local Ltac uwf_epilogue := do 10 step.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac uwf_tail IH HC size tb :=
  let K3 := fresh "K3" in let K4 := fresh "K4" in let K5 := fresh "K5" in let Etr := fresh "Etr" in
  let AL2 := fresh "AL2" in let NA2 := fresh "NA2" in
  step; if_cases K3; zify_cond K3;
  [ pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue
  | step; if_cases K4; zify_cond K4;
    [ pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue
    | do 2 zstep; step; if_cases K5; zify_cond K5;
      [ (* [comment removed for export] *)
        assert (AL2 : _ mod 8 = 0) by (change 7 with (Z.ones 3) in K5; rewrite Z.land_ones in K5 by lia; exact K5)
      | assert (NA2 : _ mod 8 <> 0) by (change 7 with (Z.ones 3) in K5; rewrite Z.land_ones in K5 by lia; exact K5);
        pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue ] ] ].

Local Ltac all_exits_post MU WM SZC TB LTB :=
  apply evtF_done; unfold uwf_post; do 6 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|]; split; [assumption|];
  split; [cbn [length app]; rewrite ?Z.add_0_r; exact SZC|]; split; [exact TB|]; split; [exact LTB|];
  split; [intros; reflexivity| reflexivity].

Local Ltac push_exits_post MU WM SZC TB LTB size :=
  apply evtF_done; unfold uwf_post; do 6 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|]; split; [assumption|];
  split; [cbn [length app]; replace (Z.of_nat size + Z.of_nat 1) with (Z.of_nat (Datatypes.S size)) by lia; exact SZC |];
  split; [exact TB|]; split; [rewrite upd_length; exact LTB|];
  split; [let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply nth_error_upd_other; lia|];
  cbn [length app]; rewrite skipn_upd_here by lia; cbn [firstn map]; rewrite unsigned_lit by lia; reflexivity.

Section CANSEC2. Context {rc : runConstT}.
Lemma uwf_loop : forall m0 top pc prev frame k tr,
  uchain m0 top pc prev frame k tr ->
  forall RNG (gp tp t0 t1 t2 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : amem)
         (S spf lo : Z) (raf s0f s1f s2f s3f s4f s5f s6f : word) (size : nat) (tb : list word),
  (forall i, frame - 16 <= i < top -> m (wa i) = m0 (wa i)) ->
  mem_inv bsegs m ->
  prev < frame -> frame < top - 16 -> frame mod 8 = 0 ->
  Z.of_nat size + Z.of_nat k = 30 -> length tb = 255%nat ->
  rw_cells bsegs m (S + 8) [C4 (Z_to_bv 64 (Z.of_nat size))] ->
  u64arr bsegs m (S + 16) tb ->
  rw_cells bsegs m spf [C8 s6f; C8 s5f; C8 s4f; C8 s3f; C8 s2f; C8 s1f; C8 s0f; C8 raf] ->
  ATOP <= lo -> lo <= spf -> spf + 64 <= S -> S + 2072 <= frame -> top <= 2^47 -> 0 <= pc < 2^64 ->
  rng RNG lo (top - lo) ->
  evtF bsegs RNG (uwf_post S pc top spf raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc size tb tr m)
    (MS (mkR raf (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 30) (Z_to_bv 64 (top - 16))
             (Z_to_bv 64 S) (Z_to_bv 64 pc) (Z_to_bv 64 frame) (Z_to_bv 64 4096) (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (Z.of_nat size)) a6 a7
             (Z_to_bv 64 APGSZ) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x75494) fc None m (seg_rom bsegs)).
Proof.
  intros m0 top pc prev frame k tr H.
  induction H as [prev frame k Hn | prev frame k fp rav H1 H2 H3 H4 B1 B2 Hra
                | prev frame k fp rav tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH];
    intros until tb; intros AG MI PF FT AL SK LTB SZC TB FR CEIL LOS SPS SPV TOP PC RR; unfold APGSZ in *.
  - (* [comment removed for export] *)
    assert (K0 : k = 0%nat) by (destruct k; [reflexivity| exfalso; apply Hn; repeat split; auto; lia]). subst k.
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    step. if_cases K; zify_cond K; [| exfalso; lia].
    uwf_epilogue.
    apply evtF_done. unfold uwf_post. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [cbn [length]; rewrite Z.add_0_r; exact SZC|]. split; [exact TB|]. split; [exact LTB|].
    split; [intros; reflexivity| reflexivity].
  - (* [comment removed for export] *)
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; lia|].
    assert (B2' : bytes_at bsegs m (frame + -8) (le8 (Z_to_bv 64 rav))).
    { eapply bytes_at_agree; [replace (frame + -8) with (frame - 8) by lia; exact B2|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    pose proof (bytes_at_read8 _ _ _ B2') as R2.
    step. clear R2 B2'.
    step. if_cases K1; zify_cond K1; [| exfalso; lia].
    uwf_epilogue.
    apply evtF_done. unfold uwf_post. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [cbn [length]; rewrite Z.add_0_r; exact SZC|]. split; [exact TB|]. split; [exact LTB|].
    split; [intros; reflexivity| reflexivity].
  - (* [comment removed for export] *)
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; lia|].
    assert (B2' : bytes_at bsegs m (frame + -8) (le8 (Z_to_bv 64 rav))).
    { eapply bytes_at_agree; [replace (frame + -8) with (frame - 8) by lia; exact B2|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    assert (B1' : bytes_at bsegs m (frame + -16) (le8 (Z_to_bv 64 fp))).
    { eapply bytes_at_agree; [replace (frame + -16) with (frame - 16) by lia; exact B1|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    pose proof (bytes_at_read8 _ _ _ B2') as R2.
    step. clear R2 B2'.
    step. if_cases K1; zify_cond K1; [exfalso; lia|].
    step. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (rav =? pc) with true in * by (symmetry; apply Z.eqb_eq; lia).
      pose proof (bytes_at_read8 _ _ _ B1') as R1.
      step. clear R1 B1'.
      uwf_tail IH HC size tb.
      * (* [comment removed for export] *)
        all_exits_post MU WM SZC TB LTB.
      * all_exits_post MU WM SZC TB LTB.
      * (* [comment removed for export] *)
        eapply evtF_mono.
        { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
            eapply (IH RNG gp tp t0 t1 t2 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm S spf lo raf s0f s1f s2f s3f s4f s5f s6f
                       size tb) end.
          all: try eassumption; try lia.
          intros i Hi. transitivity (m (wa i)); [apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia | apply AG; lia]. }
        intros ms' PO. cbn [app] in *. exact PO.
      * all_exits_post MU WM SZC TB LTB.
    + (* [comment removed for export] *)
      replace (rav =? pc) with false in * by (symmetry; apply Z.eqb_neq; lia).
      do 3 zstep.                                         (* [comment removed for export] *)
      step.                                               (* [comment removed for export] *)
      rewrite (Z.shiftl_mul_pow2 (Z.of_nat size) 3) by lia. change (2^3) with 8.
      replace (S + 16 + Z.of_nat size * 8) with (S + 16 + 8 * Z.of_nat size) by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u64arr_store_ok bsegs mm (S + 16) tb (Z.of_nat size) (wa (S + 16 + 8 * Z.of_nat size)) TB ltac:(lia) eq_refl) as SOK end.
      step.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (u64arr_write bsegs mm (S + 16) tb (Z.of_nat size) (Z_to_bv 64 rav) TB ltac:(lia)) as TB2 end.
      clear TB. store_done. rename TB2 into TB.
      pose proof (bytes_at_read8 _ _ _ B1') as R1.
      step. clear R1 B1'.
      replace (Z.of_nat size + 1) with (Z.of_nat (Datatypes.S size)) in * by lia.
      replace (Z.to_nat (Z.of_nat size)) with size in TB by lia.
      uwf_tail IH HC (Datatypes.S size) (upd tb size (Z_to_bv 64 rav)).
      * push_exits_post MU WM SZC TB LTB size.
      * push_exits_post MU WM SZC TB LTB size.
      * eapply evtF_mono.
        { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
            eapply (IH RNG gp tp t0 t1 t2 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm S spf lo raf s0f s1f s2f s3f s4f s5f s6f
                       (Datatypes.S size) (upd tb size (Z_to_bv 64 rav))) end.
          all: try eassumption; try lia.
          - intros i Hi. transitivity (m (wa i)); [apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia | apply AG; lia].
          - rewrite upd_length. exact LTB. }
        intros ms' PO. unfold uwf_post in PO |- *.
        destruct PO as (a2' & a5' & a6' & a7' & m' & tb' & -> & MU' & WM' & MI' & SZ' & TB' & LTB' & OLD & NEW).
        exists a2', a5', a6', a7', m', tb'. split; [reflexivity|].
        split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
        split; [cbn [length app]; replace (Z.of_nat size + Z.of_nat (Datatypes.S (length tr))) with (Z.of_nat (Datatypes.S size) + Z.of_nat (length tr)) by lia; exact SZ'|].
        split; [exact TB'|]. split; [exact LTB'|]. split.
        { intros i Hi. rewrite (OLD i) by lia. apply nth_error_upd_other. lia. }
        cbn [length app]. rewrite (skipn_S_nth tb' size (Z_to_bv 64 rav)).
        2:{ rewrite (OLD size) by lia. apply nth_error_upd_here. lia. }
        cbn [firstn map]. rewrite unsigned_lit by lia. f_equal. exact NEW.
      * push_exits_post MU WM SZC TB LTB size.
Qed.

(* [comment removed for export] *)
Definition unwind_fast_post (S pc top : Z) (sp : word) (raf s0f s1f s2f s3f s4f s5f s6f : word)
    (gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
    (tb : list word) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a2' a3' a4' a5' a6' a7' m' tb',
    ms' = MS (mkR raf sp gp tp t0 t1 t2 s0f s1f
                  (Z_to_bv 64 S) (Z_to_bv 64 pc) a2' a3' a4' a5' a6' a7'
                  s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc raf) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (S + 8) [C4 (Z_to_bv 64 (1 + Z.of_nat (length tr)))]
    /\ u64arr bsegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length tr)) tb') = pc :: tr.

Lemma unwind_fast_spec : forall RNG (raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp top bot lo : Z) (tb : list word) (tr : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= S ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 top -> a4 = Z_to_bv 64 bot -> a5 = Z_to_bv 64 30 ->
  rw_cells bsegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells bsegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (exists szj, rw_cells bsegs m (S + 8) [C4 szj]) -> u64arr bsegs m (S + 16) tb -> length tb = 255%nat ->
  uchain m top pc bot bp 29%nat tr ->
  0 <= bot -> bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> top <= 2^47 -> S + 2072 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng RNG lo (top - lo) ->
  evtF bsegs RNG (unwind_fast_post S pc top sp raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo tb tr m)
    (MS (mkR raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x753d4) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros ST CEIL LO SPS MI -> -> -> -> -> -> GPG PG [szj SZC] TB LTB UC B0 BB BT BA TOP SB PC RIMG RR.
  unfold GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. do 3 zstep.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 3 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_store_ok bsegs mm (S + 16) tb 0 (wa (S + 16)) TB ltac:(lia) ltac:(f_equal; lia)) as SOK end.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u64arr_write bsegs mm (S + 16) tb 0 (Z_to_bv 64 pc) TB ltac:(lia)) as TB2;
    rewrite Z.mul_0_r, Z.add_0_r in TB2 end.
  clear TB. store_done. rename TB2 into TB. cbn [Z.to_nat upd] in TB.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in K0 by lia. Z.div_mod_to_equations. lia. }
  step. if_cases K1; zify_cond K1. { exfalso. lia. }     (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  zstep. step. if_cases K4; zify_cond K4.                (* [comment removed for export] *)
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact BA. }
  zstep. step.                                 (* [comment removed for export] *)
  replace (top + -16) with (top - 16) by lia.
  change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)).
  eapply evtF_mono.
  { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (uwf_loop m top pc bot bp 29 tr UC RNG gp tp t0 t1 t2 _ _ _ _ _ _ s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm
                S (bv_unsigned sp + -64) lo raf s0f s1f s2f s3f s4f s5f s6f 1%nat (upd tb 0 (Z_to_bv 64 pc))) end.
    all: try eassumption; try lia.
    - intros i Hi. apply MU. unfold wa. rewrite unsigned_lit by lia. cbn. lia.
    - rewrite upd_length. exact LTB. }
  intros ms' PO. unfold uwf_post in PO. unfold unwind_fast_post.
  destruct PO as (a2' & a5' & a6' & a7' & m' & tb' & -> & MU' & WM' & MI' & SZ' & TB' & LTB' & OLD & NEW).
  exists a2', (Z_to_bv 64 4096), (Z_to_bv 64 (S + 16)), a5', a6', a7', m', tb'.
  split. { replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. intros x Hx. cbn in Hx |- *. tauto. }
  split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
  split. { (* [comment removed for export] *)
    match goal with FRH : rw_cells bsegs ?mx (bv_unsigned sp + -64) ?cs, STH : stk bsegs ?mx' lo _ |- _ =>
      constr_eq mx mx';
      pose proof (rw_cells_transport bsegs _ _ _ _ cs FRH MU' WM' ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
      pose proof (stk_transport_disjoint bsegs _ _ _ _ _ STH MU' WM' ltac:(cbn [disjoint_from]; lia)) as ST'
    end.
    eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
    replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in FR' by lia. exact FR'. }
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|].
  destruct tb' as [|w tb'']; [cbn in LTB'; lia|].
  specialize (OLD 0%nat ltac:(lia)). cbn [nth_error] in OLD.
  destruct tb as [|w0 tb0]; [cbn in LTB; lia|]. cbn in OLD. injection OLD as ->.
  cbn [firstn map skipn] in NEW |- *. rewrite unsigned_lit by lia. f_equal. exact NEW.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC2.
Notation unwind_impl_W sp S t :=
  ([(bv_unsigned sp - 160, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056); (S + 2056, S + 2064); (t + 3168, t + 3169)]%Z) (only parsing).

Section CANSEC3. Context {rc : runConstT}.
Definition unwind_impl_post (S pc bp t : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' tb',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (unwind_impl_W sp S t) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (S + 8) [C4 (Z_to_bv 64 (1 + Z.of_nat (length tr)))]
    /\ u64arr bsegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length tr)) tb') = pc :: tr
    /\ rw_cells bsegs m' (S + 2056) [C8 (Z_to_bv 64 bp)]
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Lemma unwind_impl_spec : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp ctx t top bot lo : Z) (tb : list word) (tr : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp <= S ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 30 ->
  (* [comment removed for export] *)
  rw_cells bsegs m AINITED [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells bsegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells bsegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  (exists szj, rw_cells bsegs m (S + 8) [C4 szj]) -> u64arr bsegs m (S + 16) tb -> length tb = 255%nat ->
  (exists bpj, rw_cells bsegs m (S + 2056) [C8 bpj]) ->
  (* [comment removed for export] *)
  uchain m top pc bot bp 29%nat tr ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  0 <= bot -> bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> top <= 2^47 -> S + 2080 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng RNG lo (top - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (unwind_impl_post S pc bp t ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo tr m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5c91c) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros ST CEIL LO SPS MI TP -> -> -> -> -> -> INI TI TK T88 TSD CT GPG PG TT SW UW [szj SZC] TB LTB [bpj BPJ] UC
         C0 C1 T0 T1 CT2 B0 BB BT BA TOP SB PC RIMG RR RCTX RT. unfold sclr, iclr, KLS, AIMG_LO in *.   (* [comment removed for export] *)
  unfold AIMG_HI, AINITED, ATSDI, ATSDK, ATP88, ATSD, GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl (unwind_impl_W sp S t) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.        (* [comment removed for export] *)
  box RT.   (* [comment removed for export] *)
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. rename POST into ST. try rename MI0 into MI.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI end.
  step. if_cases K; zify_cond K; [exfalso; lia|].     (* [comment removed for export] *)
  zstep. lstep. step. step.                           (* [comment removed for export] *)
  step. if_lit.                                       (* [comment removed for export] *)
  step. step. callp stack_top_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  do 3 step. callp stack_bottom_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  step. step. if_lit.                                 (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 8 step.                                          (* [comment removed for export] *)
  do 6 zstep.                                         (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615.
  rewrite (land_ones_l bp) by lia.
  step.                                               (* [comment removed for export] *)
  step. if_lit. step. if_lit. step. if_lit.           (* [comment removed for export] *)
  do 5 step.                                          (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -80).
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (UC' : uchain mm top pc bot bp 29 tr)
      by (eapply uchain_frame; [exact UC|]; intros a Ha; apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia) end.
  name_sp sp (-80). rewrite <- Hsp in ST.
  eapply evtF_cut.
  { eapply unwind_fast_spec;
    [ exact ST | exact CEIL | | | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | exact GPG | exact PG | eexists; exact SZC | exact TB | exact LTB | exact UC' | | | | exact BA | | | exact PC
    | exact RIMG | exact RR ].
    all: lia. }
  cbv beta. unfold unwind_fast_post.
  lazymatch goal with |- forall ms', _ -> evtF _ _ _ _ => idtac end.
  lazymatch type of MU with munch _ _ ?mcur => post_call bsegs mcur end.
  unname_sp.
  clear UC'. rename PC0 into ST. rename PC1 into SZ'. rename PC2 into TB'. rename PC3 into LTB'. rename POST into TR'.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI' end.
  (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  do 12 step.                                         (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_impl_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|]. split; [exact TR'|].
  split; assumption.
Qed.
End CANSEC3.
