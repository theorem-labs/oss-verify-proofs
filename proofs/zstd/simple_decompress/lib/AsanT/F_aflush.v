(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AKit AKit2 ARep RT_stubs F_ammap F_apoison APoisonR_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition flush_entry := 0x54bd0.
End CANSEC1.
Abbreviation FLUSH_STACK := 64.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma mem_to_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p : Z),
  mem_inv bsegs m -> poison_cells m ->
  (0 <= p /\ p + 1 <= 0x7fff8000 \/ 0x10007fff8000 <= p) -> p <= 0x7fffffffffff ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a1' a2' a3' a4' a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (shad p)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54c1c) fc None m (seg_rom bsegs)).
Proof.
  intros until p. intros MI PC PLO PHI RA RIMG.
  destruct PC as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [exfalso; lia|].           (* [comment removed for export] *)
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: change (2147450880 + Z.shiftr p 3) with (shad p).
  all: step.                                           (* [comment removed for export] *)
  all: apply evtF_done; do 8 eexists; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma apply_zeros_same : forall (m : amem) A L a n,
  rw_cells bsegs m A [CB (Z.to_nat L) (zeros L)] -> 0 <= L ->
  0x625000 <= A -> A <= a -> 0 < n -> a + n <= A + L ->
  apply_zeros m [(wa a, Z_to_bv 64 n)] = m.
Proof.
  intros m A L a n SHZ HL HA Ha Hn Han.
  pose proof (rw_cells_bound bsegs m A _ SHZ) as HB. cbn [cells_size csize Nat.add] in HB. rewrite Nat.add_0_r, Z2Nat.id in HB by lia.
  pose proof (rw_cells_bytes_at bsegs m A _ SHZ) as (_ & _ & BY). cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  apply functional_extensionality. intros x.
  rewrite apply_zeros_spec by lia. unfold in_range.
  destruct (Z.leb_spec a (bv_unsigned x)) as [H1|H1]; [|reflexivity].
  destruct (Z.ltb_spec (bv_unsigned x) (a + n)) as [H2|H2]; [|reflexivity]. cbn [andb].
  specialize (BY (Z.to_nat (bv_unsigned x - A))). unfold zeros in BY. rewrite repeat_length in BY.
  specialize (BY ltac:(lia)). rewrite Z2Nat.id in BY by lia.
  replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in BY by lia.
  unfold wa in BY. rewrite Z_to_bv_bv_unsigned in BY.
  rewrite ref_mrd_overlay in BY by lia. rewrite BY.
  rewrite nth_error_repeat by lia. reflexivity.
Qed.

Definition flush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition flush_tree {R} (mb ms : Z) (T : itree node (exc R)) : itree node (exc R) :=
  if flush_beg mb <? flush_end mb ms
  then ebind (enode (NMadvise (flush_beg mb) (flush_end mb ms - flush_beg mb))
                    (adec_madvise (flush_beg mb) (flush_end mb ms - flush_beg mb))) (fun _ => T)
  else T.

Lemma flush_spec : forall RNG {R} (T : itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->        (* [comment removed for export] *)
  mb mod 8 = 0 -> ms mod 8 = 0 ->
  rw_cells bsegs m (shad mb) [CB (Z.to_nat (shlen ms)) (zeros (shlen ms))] ->     (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall ms', flush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms' ->
      implS bsegs RNG T (epostF Q) ms') ->
  implS bsegs RNG (flush_tree mb ms T) (epostF Q)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 flush_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI PC PRM RR -> -> MLO MPOS MCE MB8 MS8 SHZ RA RIMG RSTK KONT.
  unfold flush_entry in *. word_range sp SPR. pose proof MLO as MBND. unfold ablk, AIMG_HI, KLS in MLO. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof PRM as PRM0. destruct PRM0 as (GPG & PGSZ & MLIM & F216 & F240 & CAN & LPG).
  pose proof (munch_refl [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  assert (SEAL : rw_cells bsegs m 0xc7348 [C8 (Z_to_bv 64 1)]).
  { eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xc7348 (le8 (Z_to_bv 64 1)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  (* [comment removed for export] *)
  pose proof (rw_cells_bound bsegs m (shad mb) _ SHZ) as SHB. cbn [cells_size csize Nat.add] in SHB.
  assert (SHL : shlen ms = ms / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHM : shad (mb + ms) = shad mb + shlen ms).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -MB8 MS8. Z.div_mod_to_equations. lia. }
  assert (SH0 : 2147450880 <= shad mb) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MLO MPOS; Z.div_mod_to_equations; lia).
  rewrite Nat.add_0_r, Z2Nat.id in SHB by (rewrite SHL; clear -MPOS; Z.div_mod_to_equations; lia).
  assert (SH1 : shad mb + shlen ms <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -MB8 MS8 MPOS MLO MCE ATR. Z.div_mod_to_equations. lia. }
  box SHZ.
  iprefix.
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & ->).
  replace (ret_pc (Z_to_bv 64 347120)) with (Z_to_bv 64 347120 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. zstep.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (mb + ms)) ltac:(f_equal; clear; lia).
  step.                                                        (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (b1' & b2' & b3' & b4' & b5' & b6' & b7' & u0' & ->).
  replace (ret_pc (Z_to_bv 64 347132)) with (Z_to_bv 64 347132 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. step.                                                  (* [comment removed for export] *)
  do 5 step.                                                   (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.                                                        (* [comment removed for export] *)
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (EB : flush_beg mb = shad mb + 4095 - (shad mb + 4095) mod 4096).
  { unfold flush_beg, rup, PG, SHADOW_OFF, shad, ASHOFF. clear. Z.div_mod_to_equations. lia. }
  assert (EE : flush_end mb ms = shad (mb + ms) - shad (mb + ms) mod 4096).
  { unfold flush_end, rdn, PG, SHADOW_OFF, shad, ASHOFF. clear. Z.div_mod_to_equations. lia. }
  setreg 10 (Z_to_bv 64 (flush_beg mb)) ltac:(rewrite ?(Z.mod_small (shad mb + 4095)) by (clear -SH0 SH1 MPOS SHL; rewrite SHL in SH1; Z.div_mod_to_equations; lia); rewrite land_align4096 by (clear -SH0 SH1 MPOS SHL; rewrite SHL in SH1; Z.div_mod_to_equations; lia); f_equal; rewrite EB; clear; lia).
  setreg 11 (Z_to_bv 64 (flush_end mb ms)) ltac:(rewrite land_align4096 by (rewrite SHM; clear -SH0 SH1 MPOS SHL; rewrite SHL in *; Z.div_mod_to_equations; lia); f_equal; rewrite EE; clear; lia).
  assert (FB : shad mb <= flush_beg mb /\ flush_beg mb < shad mb + 4096) by (rewrite EB; clear; Z.div_mod_to_equations; lia).
  assert (FE : flush_end mb ms <= shad mb + shlen ms /\ shad mb + shlen ms < flush_end mb ms + 4096) by (rewrite EE, SHM; clear; Z.div_mod_to_equations; lia).
  unfold flush_tree.
  step. if_cases KR; zify_cond KR.                             (* [comment removed for export] *)
  - (* [comment removed for export] *)
    do 5 step.                                                 (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -32) _ |- _ =>
      lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
    step.                                                      (* [comment removed for export] *)
    apply evtF_done.
    rewrite (proj2 (Z.ltb_ge (flush_beg mb) (flush_end mb ms))) by (clear -KR SHB SH0 FB FE; rewrite ?unsigned_lit in KR by lia; lia).
    apply KONT. unfold flush_post. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
  - zstep. step.                                               (* [comment removed for export] *)
    do 5 step.                                                 (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -32) _ |- _ =>
      lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
    step.                                                      (* [comment removed for export] *)
    step. step. step. if_lit.                                  (* [comment removed for export] *)
    step. step. if_lit.                                        (* [comment removed for export] *)
    assert (LT : flush_beg mb < flush_end mb ms) by (clear -KR SHB SH0 FB FE; rewrite ?unsigned_lit in KR by lia; lia).
    setreg 11 (Z_to_bv 64 (flush_end mb ms - flush_beg mb)) ltac:(f_equal; clear -LT SHB SH0 FB FE; lia).
    apply evtF_done.
    rewrite (proj2 (Z.ltb_lt (flush_beg mb) (flush_end mb ms)) LT).
    eapply (implF_ebind _ _ _ _ _ _ _ (fun (_ : Z) RNG' ms' => RNG' = RNG /\
              flush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms')).
    2: { intros a RNG' ms' (-> & PO). apply KONT. exact PO. }
    (* [comment removed for export] *)
    apply implF_enode.
    step. step_ecall. split. { at_nodeA_solve. }               (* [comment removed for export] *)
    intros rsp RNG' a HF Hdec.
    destruct (adec_madvise_Some _ _ _ _ Hdec) as (-> & ci & ->).
    assert (ERNG : RNG' = RNG) by (destruct HF as [HA _]; exact HA). subst RNG'.
    rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in
        replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
    end.
    cbn [eff_ret]. rewrite eff_mem_zeros.
    (* [comment removed for export] *)
    assert (PRU : mmap_len (flush_end mb ms - flush_beg mb) = flush_end mb ms - flush_beg mb).
    { unfold mmap_len. apply page_round_up_mult; [rewrite EB, EE; clear; Z.div_mod_to_equations; lia | clear -LT; lia]. }
    rewrite PRU.
    (* [comment removed for export] *)
    carry SHZ MU WM ltac:(rewrite Nat.add_0_r, Z2Nat.id by (clear -SHL MPOS; rewrite SHL; Z.div_mod_to_equations; lia); clear -SH1 SPR CEIL LO ATR; lia).
    change (Z_to_bv 64 (flush_beg mb)) with (wa (flush_beg mb)).
    rewrite (apply_zeros_same _ (shad mb) (shlen ms) (flush_beg mb) (flush_end mb ms - flush_beg mb) SHZ)
      by (clear -LT SHB SH0 FB FE MPOS SHL; first [lia | rewrite SHL; Z.div_mod_to_equations; lia]).
    zstep. step.                                               (* [comment removed for export] *)
    apply evtF_done. split; [reflexivity|]. unfold flush_post. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
Qed.
End CANSEC2.
