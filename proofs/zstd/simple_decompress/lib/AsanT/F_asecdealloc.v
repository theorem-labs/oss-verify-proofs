(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanCtrlProps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AKit AKit2 AKitQ ARep ARepKit ARepFrame F_agbb
     F_memset F_apoison APoisonR_iface F_apoisonz F_aalloc3 F_aflush F_aunmap AFrameD.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
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
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?AD (le8 ?v)) _) =>
      let E := lazymatch AD with wa ?E => E | Z_to_bv 64 ?E => E end in
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_hd1 : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app bsegs m A [c] cs)) in H as [H _]. exact H. Qed.

Definition sdealloc_entry := 0x36120.
(* [comment removed for export] *)
End CANSEC1.
Abbreviation SDEALLOC_STACK := 624.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition sdealloc_k {R} (k : astate -> AM R) (st : astate) : Z -> AM R :=
  fun r => let st1 := set_nsec (a_nsec st - 1) st in
           if r =? 0 then k st1 else if is_err r then aundef_ USpin (k st1) else aundef_ UBadAnswer (k st1).

(* [comment removed for export] *)
Definition sdealloc_m {R} (k : astate -> AM R) (st : astate) (mb ms : Z) : AM R :=
  if flush_beg mb <? flush_end mb ms
  then ev (AMadvise (flush_beg mb) (flush_end mb ms - flush_beg mb)) (fun _ => ev (AMunmap mb ms) (sdealloc_k k st))
  else ev (AMunmap mb ms) (sdealloc_k k st).

Lemma large_dealloc_unfold : forall {R} (st : astate) mb ms (k : astate -> AM R),
  large_dealloc st mb ms k = poison0 mb ms (sdealloc_m k st mb ms).
Proof. reflexivity. Qed.

Lemma aembed_sdealloc_m : forall {R} (k : astate -> AM R) (st : astate) mb ms,
  aembed ATOP (sdealloc_m k st mb ms) = flush_tree mb ms (aembed ATOP (ev (AMunmap mb ms) (sdealloc_k k st))).
Proof.
  intros R k st mb ms. unfold sdealloc_m, flush_tree. destruct (flush_beg mb <? flush_end mb ms); [|reflexivity].
  unfold ev at 1. rewrite aembed_vis. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sdealloc_tail_W (sp0 t mb ms : Z) : list (Z * Z) :=
  [(sp0 - 96, sp0); (t + 2800, t + 3168); (mb, mb + ms)]%Z.

Lemma sdealloc_tail_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    (sp ra0 s0v s1v s2v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms ctx t lo : Z) (hsz hix : word) (sj : list word),
  stk bsegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 hix] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m (shad mb) [CB (Z.to_nat (shlen ms)) (zeros (shlen ms))] ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcf560 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xcf564 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  4096 <= bv_unsigned ra0 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG mb 32 ->
  (* [comment removed for export] *)
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap mb ms) rsp RNG RNG' ->
      munch (sdealloc_tail_W (bv_unsigned sp) t mb ms) m m' -> mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) ->
      (exists sj', u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat) ->
      implS bsegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra0 sp gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (sdealloc_m k st mb ms)) (epostF Q)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 mb) (Z_to_bv 64 mb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ms) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x36214) fc None m (seg_rom bsegs)).
Proof.
  intros until sj. intros ST CEIL LO SPHI MI TP FR HDR MBAL MLO MPOS MAL MCE SHZ TI TK T88 TSD CT CX0 CX1 T0 T1 DMT DMC STATS LSJ
         PC PRM RR RA RIMG RSTK RCTX RT RMB KONT. band_lin.   (* [comment removed for export] *)
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4).   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  assert (MS4 : 4096 <= ms) by (clear -MPOS MAL; Z.div_mod_to_equations; lia).
  pose proof (munch_refl (sdealloc_tail_W (bv_unsigned sp) t mb ms) m) as MU. unfold sdealloc_tail_W in MU.
  box HDR. box STATS. box CT. box TSD.
  rewrite aembed_sdealloc_m.
  iprefix.
  step. step.                                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done.
  eapply (flush_spec RNG (aembed ATOP (ev (AMunmap mb ms) (sdealloc_k k st))) Q) with (mb := mb) (ms := ms) (lo := lo).
  all: lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- premap_cells _ => exact PRM
         | |- arelro0 _ => exact RR
         | |- ablk _ _ => exact MLO   (* [comment removed for export] *)
         | |- @eq word _ _ => reflexivity
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -SPHI CEIL LO LO0 SPR; lia
         | |- rw_cells _ _ (shad _) _ => exact SHZ
         | |- _ mod 8 = 0 => first [clear -MBAL; Z.div_mod_to_equations; lia | clear -MAL; Z.div_mod_to_equations; lia]
         | |- forall _, _ => idtac
         | |- _ => atop_facts; rewrite ?unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MPOS MCE RA; lia
         end.
  intros ms' PO. unfold flush_post in PO. destruct_exs PO. destruct PO as (-> & MU1 & WM1 & MI1 & ST1).
  iprefix.
  rewrite !unsigned_lit in MU1, ST1 by (clear -SPHI CEIL LO LO0 SPR; lia).
  replace (ret_pc (Z_to_bv 64 221728)) with (Z_to_bv 64 221728 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport FR MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  xport TI MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). xport TK MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). xport T88 MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  carry TSD MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). carry CT MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR CX0 CX1; lia).
  carry STATS MU1 WM1 ltac:(rewrite LSJ; clear -SPHI CEIL LO LO0 SPR T0 T1; lia).
  carry HDR MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MCE MS4; lia).
  pose proof (poison_cells_frame _ _ _ PC MU1 WM1 ltac:(apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPHI CEIL LO LO0 SPR; lia | apply Forall_nil])) as PC1.
  pose proof (arelro0_munch _ _ _ RR MU1 ltac:(apply Forall_cons; [cbn; unfold ARELRO_LO, ARELRO_HI; clear -SPHI CEIL LO LO0 SPR; lia | apply Forall_nil])) as RR1.
  lazymatch type of MU1 with munch _ _ ?mm =>
    assert (MU1' : munch [(bv_unsigned sp - 96, bv_unsigned sp); (t + 2800, t + 3168); (mb, mb + ms)]%Z m mm) end.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia. }
  clear MU MU1 WM1 MI RR. rename MI1 into MI. rename MU1' into MU.
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  box HDR. box STATS. box CT. box TSD.
  eapply evtF_cut.
  { eapply (thread_stats_spec RNG ctx t lo).
    all: lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); exact ST1
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- rw_cells _ _ (_ + 152) _ => unboxed CT
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 _)] => first [eassumption | unboxed TSD]
         | |- rw_cells _ _ _ _ => eassumption
         | |- iclr _ _ => exact T0   (* [comment removed for export] *)
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ 4096 => exact RCTX
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -SPHI CEIL LO LO0 SPR; lia
         | |- _ => unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); clear -SPHI CEIL LO LO0 SPR CX0 CX1 T0 T1; lia
         end. }
  cbv beta. intros ms' PO. destruct PO as (a1q & mq & -> & MU0 & WM0 & MI0 & ST0).
  rewrite !unsigned_lit in MU0, ST0 by (clear -SPHI CEIL LO LO0 SPR; lia).
  replace (ret_pc (Z_to_bv 64 221732)) with (Z_to_bv 64 221732 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  clear ST1. try clear ST. rename ST0 into ST.
  carry STATS MU0 WM0 ltac:(rewrite LSJ; clear -SPHI CEIL LO LO0 SPR T0 T1; lia).
  carry HDR MU0 WM0 ltac:(clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MCE MS4; lia).
  xport FR MU0 WM0 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  lazymatch type of MU0 with munch _ _ ?mm =>
    assert (MU2 : munch [(bv_unsigned sp - 96, bv_unsigned sp); (t + 2800, t + 3168); (mb, mb + ms)]%Z m mm) end.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU0]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia. }
  clear MU MU0 WM0 MI. rename MI0 into MI. rename MU2 into MU.
  pose proof (rng_sub _ _ _ (t + 2800) 368 RT ltac:(clear; lia) ltac:(clear; lia)) as RSJ.
  aload STATS 12 (t + 2800 + 96).                              (* [comment removed for export] *)
  aload STATS 11 (t + 2800 + 88).                              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  astore STATS 11.                                             (* [comment removed for export] *)
  astore STATS 12.                                             (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 5 step.                                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. rewrite aembed_vis. cbn [aev_tree].
  eapply (unmap_or_die_spec RNG (fun z => aembed ATOP (sdealloc_k k st z)) Q) with (addr := mb) (size := ms) (lo := lo).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- @eq word _ _ => reflexivity
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ _ => exact RSTK
       | |- unmap_cells _ =>
           (* [comment removed for export] *)
           destruct PC as (G6 & _); destruct PRM as (_ & _ & ML & _); apply rw_cells_hd1 in G6;
           split; (eapply cells_frameD; [eassumption | exact MU | cbn; unfold AIMG_HI in *; clear -SPHI CEIL LO LO0 SPR T0 MLO ML1 ML2 ML3; lia])
       | |- forall _, _ => idtac
       | |- _ => unfold AIMG_HI; clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MPOS MAL MCE RA; lia
       end.
  (* [comment removed for export] *)
  intros rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MUu MIu STu UCu.
  unfold sdealloc_k. rewrite Z.eqb_refl.
  eapply KONT; [exact HF | | exact MIu | exact STu |].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUu]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
  - eexists. split; [eapply u64arr_frameD; [exact STATS | exact MUu |] | rewrite !upd_length; exact LSJ].
    rewrite !upd_length, LSJ. cbn. clear -SPHI CEIL LO LO0 SPR T0 T1 DMT. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nth_map_lit : forall (l : list Z) i x, nth_error l i = Some x -> nth i (map (Z_to_bv 64) l) (Z_to_bv 64 0) = Z_to_bv 64 x.
Proof.
  intros l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma c8x4_of_junk32 : forall m A, junk_at m A 32 -> exists w1 w2 w3 w4 : word, rw_cells bsegs m A [C8 w1; C8 w2; C8 w3; C8 w4].
Proof.
  intros m A J. destruct (junk_split m A 16 16 J ltac:(lia) ltac:(lia)) as [J1 J2].
  destruct (c8c8_of_junk m A J1) as (w1 & w2 & H1). destruct (c8c8_of_junk m (A + 16) J2) as (w3 & w4 & H2).
  exists w1, w2, w3, w4. apply (proj2 (rw_cells_app bsegs m A [C8 w1; C8 w2] [C8 w3; C8 w4])). split; [exact H1| exact H2].
Qed.

Lemma junk_of_cells' : forall m A cs n, rw_cells bsegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof. intros m A cs n H <-. apply junk_of_cells. exact H. Qed.

(* [comment removed for export] *)
Definition sdealloc_W (sp t mb ms PA idx last : Z) : list (Z * Z) :=
  [(sp - SDEALLOC_STACK, sp); (t + 2800, t + 3168);
   (0xcc710, 0xcc719); (0xcc728, 0xcc738); (0xcc940, 0xcc944); (0xcc958, 0xcc968);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)]%Z.

(* [comment removed for export] *)
Definition sdealloc_post (sp : word) (t mb ms PA nres nsec idx last lo : Z) (bases : list Z) (lw1 lw2 : word)
    (m m' : amem) : Prop :=
     munch (sdealloc_W (bv_unsigned sp) t mb ms PA idx last) m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' 0xcc708 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nsec - 1))]
  /\ rw_cells bsegs m' 0xcc718 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xcc720 32
  /\ rw_cells bsegs m' 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xcc958 16
  /\ u64arr bsegs m' PA (upd (map (Z_to_bv 64) bases) (Z.to_nat idx) (Z_to_bv 64 last))
  /\ (idx <> nsec - 1 -> rw_cells bsegs m' last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 idx)])
  /\ (exists sj', u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells bsegs m' (shad mb) [CB (Z.to_nat (shlen ms)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen ms)))].

Lemma sdealloc_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms idx PA nres nsec last ctx t lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt : byte) (sj : list word) (shj : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SDEALLOC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xcc6d8 -> a1 = Z_to_bv 64 0xcc948 -> a2 = Z_to_bv 64 (mb + 4096) ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcc6d8 [C8 (Z_to_bv 64 4096)] -> rw_cells bsegs m 0xcc6e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells bsegs m 0xcc708 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0xcc718 [C1 srt] -> junk_at m 0xcc720 32 ->
  rw_cells bsegs m 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xcc958 16 ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcf560 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xcf564 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr bsegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells bsegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells bsegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)) ->
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS bsegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 sdealloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until shj.
  intros ST CEIL LO SPHI MI TP -> -> -> I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR MAL MLO MPOS MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT RA
         RIMG RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  pose proof (ablk_lin _ _ PA0) as (PL1 & PL2 & PL3 & PL4). pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4).   (* [comment removed for export] *) unfold AIMG_HI in PL1, ML1.
  pose proof PA0 as PBND; pose proof MLO as MBND; unfold ablk, AIMG_HI, KLS in PBND, MBND. unfold AIMG_HI in CXI.   (* [comment removed for export] *)
  pose proof CX0 as CBND; pose proof T0 as TBND; unfold sclr, KLS in CBND, TBND.   (* [comment removed for export] *)
  assert (ASD : mb + ms <= shad mb \/ shad mb + shlen ms + 8 <= mb) by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND MAL MSAL MCE MPOS; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold ATP88, ATSD, sdealloc_entry in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  assert (MS4 : 4096 <= ms) by (clear -MPOS MSAL; Z.div_mod_to_equations; lia).
  assert (LENm : length (map (Z_to_bv 64) bases) = Z.to_nat nsec) by (rewrite length_map; clear -LEN; lia).
  rewrite large_dealloc_unfold.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - SDEALLOC_STACK, bv_unsigned sp); (0xcc710, 0xcc719); (0xcc728, 0xcc738);
                          (0xcc940, 0xcc944); (0xcc958, 0xcc968); (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - SDEALLOC_STACK, bv_unsigned sp); (0xcc710, 0xcc719); (0xcc728, 0xcc738);
                          (0xcc940, 0xcc944); (PA + 8 * idx, PA + 8 * idx + 8)]%Z m) as MUb.
  (* [comment removed for export] *)
  box TI. box TK. box T88. box TSD. box CT. box STATS. box SH. box LHDR. box DMT. box DMC. box DMP. box DPT. box DPC. box DCT.
  destruct (c8x4_of_junk32 _ _ JST) as (j0 & j1 & j2 & j3 & JS4). clear JST.
  destruct (c8c8_of_junk _ _ JGL) as (g0 & g1 & GL2). clear JGL.
  iprefix.
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 0) ltac:(f_equal; change 4095 with (2^12 - 1); rewrite zb_land_mask_l by (clear; lia); change (2^12) with 4096; clear -MAL; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep. step.                                    (* [comment removed for export] *)
  apply (gbb_mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 837952) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 mb) ltac:(f_equal; clear; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (PA + 8 * idx)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -IDX; lia).
  pose proof (rng_sub _ _ _ (PA + 8 * idx) 8 RPA ltac:(clear -IDX NSR; lia) ltac:(clear -IDX NSR; lia)) as RDi.
  aload ARR idx (PA + 8 * idx).                                (* [comment removed for export] *)
  first [rewrite (nth_map_lit _ _ _ NTHI) | unfold w0; rewrite (nth_map_lit _ _ _ NTHI)].
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 IDX NSR PA0 PL1 PL2 PL3 PA1 NRB PBND. rewrite ?unsigned_lit in K2 by lia. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep.                                          (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -IDX; lia).
  step. step.                                                  (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  pose proof (rng_sub _ _ _ (PA + 8 * (nsec - 1)) 8 RPA ltac:(clear -IDX NSR; lia) ltac:(clear -IDX NSR; lia)) as RDl.
  aload ARR (nsec - 1) (PA + 8 * nsec + -8).                   (* [comment removed for export] *)
  first [rewrite (nth_map_lit _ _ _ NTHL) | unfold w0; rewrite (nth_map_lit _ _ _ NTHL)].
  zstep. zstep.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  box HDR. snapshot [(PA + 8 * idx, PA + 8 * idx + 8)]%Z MUa WMa.
  astore ARR idx.                                              (* [comment removed for export] *)
  carry HDR MUa WMa ltac:(ub DMP; clear -Y IDX NSR MS4; lia). clear MUa WMa.
  (* [comment removed for export] *)
  destruct (Z.eq_dec idx (nsec - 1)) as [EQI | NEI];
  [ (* [comment removed for export] *)
    clear MUb;
    assert (last = mb) as ELM by (rewrite <- EQI in NTHL; rewrite NTHI in NTHL; injection NTHL as E; symmetry; exact E);
    subst last;
    pose proof MLO as LLO; pose proof ML1 as LL1; pose proof MBND as LBND; assert (LCE : mb + 32 <= ATOP) by (clear -MCE MS4; lia);   (* [comment removed for export] *)
    box ARR; snapshot [(mb + 24, mb + 32)]%Z MUl WMl;
    step;
    carry ARR MUl WMl ltac:(ub DMP; rewrite ?upd_length, LENm; clear -Y IDX NSR MS4; lia); clear MUl WMl
  | (* [comment removed for export] *)
    unbox LHDR; destruct (LHDR NEI) as (LH & LLO & LCE & LDM & LDT & LDC & LDP); clear LHDR;
    pose proof (ablk_lin _ _ LLO) as (LL1 & _ & _ & _); unfold AIMG_HI in LL1; pose proof LLO as LBND; unfold ablk, AIMG_HI, KLS in LBND;   (* [comment removed for export] *)
    pose proof (RLH NEI) as RLH';
    xport LH MUb WM ltac:(clear -LDP LLO LCE CEIL LO SPR IDX NSR LL1; lia); clear MUb;
    box ARR; box HDR; box LDM; box LDT; box LDC; box LDP;
    snapshot [(last + 24, last + 32)]%Z MUl WMl;
    step;
    carry ARR MUl WMl ltac:(ub LDP; rewrite ?upd_length, LENm; clear -Y IDX NSR; lia);
    carry HDR MUl WMl ltac:(ub LDM; clear -Y MS4; lia); clear MUl WMl ].
  (* [comment removed for export] *)
  all: assert (AMO1 : amo_aligned AD (Z_to_bv 64 0xcc958) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO1.                                         (* [comment removed for export] *)
  all: step; zstep; zstep.                                     (* [comment removed for export] *)
  all: assert (AMO2 : amo_aligned AD (Z_to_bv 64 0xcc960) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO2.                                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply (gbb_mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; step; step.                           (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  all: assert (SHR : 0x800bca00 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND ML1 ML2 ML3 MCE MS4; Z.div_mod_to_equations; lia).
  all: assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  all: assert (MSAL8 : ms mod 8 = 0) by (clear -MSAL; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport bsegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR PA0 PL1 PL2 PL3 IDX MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB NSR; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia|]); apply Forall_nil)).
  (* [comment removed for export] *)
  all: eapply (poison0_spec R (sdealloc_m k st mb ms) Q RNG) with (addr := mb) (size := ms) (lo := lo).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ _ => exact SH
       | |- rng_aimg _ => exact RIMG
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
       | |- forall _, _ => idtac
       | |- ablk _ _ => exact MLO   (* [comment removed for export] *)
       | |- _ => unfold PZR_STACK; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 MPOS MAL8 MSAL8 MCE; lia
       end.
  all: intros RNG1 mP t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PP.
  all: destruct PP as (LE1 & MUp & WMp & MI1 & ST1 & SHZ & PC1 & PRM1 & RR1); unfold PZR_STACK in MUp.
  all: rewrite !unsigned_lit in MUp, ST1 by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 221716)) with (Z_to_bv 64 221716 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: xport FR MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport HDR MUp WMp ltac:(clear -CEIL LO SPR SHR MLO ML1 ML2 ML3 MS4 MCE MBND ASD; lia).
  all: xport ARR MUp WMp ltac:(rewrite ?length_map; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 PA1 IDX NSR LEN PBND NRB; lia).
  all: xport NSC MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport SRT MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport JS4 MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport MTX MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport GL2 MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: try (xport LH MUp WMp ltac:(clear -CEIL LO SPR SHR LLO LCE LL1 LBND; lia)).
  (* [comment removed for export] *)
  all: lazymatch type of MU with munch ?Wc ?me ?mk => lazymatch type of MUp with munch ?Wp _ ?m1' =>
         assert (MU01 : munch (Wc ++ Wp) me m1') by (eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUp]];
            let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans bsegs _ _ _ WM WMp) as WM01; cbn [app] in MU01 end end.
  all: carry TI MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry TK MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry T88 MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry TSD MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry CT MU01 WM01 ltac:(first [ub LDC | pose proof I as Y]; ub DPC; ub DMC; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO CX0 CX1 MS4 Y Y0 Y1 LL1 CXI PBND MBND ASD LBND NRB CBND; lia).
  all: carry STATS MU01 WM01 ltac:(rewrite LSJ; first [ub LDT | pose proof I as Y]; ub DPT; ub DMT; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO T0 T1 MS4 Y Y0 Y1 LL1 TIC PBND MBND ASD LBND NRB TBND; lia).
  (* [comment removed for export] *)
  all: pose proof (rng_fp_le _ _ _ _ LE1 RSTK) as RSTK1; pose proof (rng_fp_le _ _ _ _ LE1 RCTX) as RCTX1;
       pose proof (rng_fp_le _ _ _ _ LE1 RT) as RT1; pose proof (rng_fp_le _ _ _ _ LE1 RMB) as RMB1; pose proof (rng_fp_le _ _ _ _ LE1 RIMG) as RIMG1.
  (* [comment removed for export] *)
  all: eapply (sdealloc_tail_spec RNG1 k st Q sp ra s0 s1 s2) with (lo := lo) (ctx := ctx) (t := t) (sj := sj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST1
       | |- mem_inv _ _ => exact MI1
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact RR1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => first [exact FR | exact HDR]
       | |- rw_cells _ _ (shad _) _ => exact SHZ   (* [comment removed for export] *)
       | |- _ mod 4096 = 0 => first [exact MAL | exact MSAL]
       | |- rw_cells _ _ _ _ => assumption
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- rng_aimg _ => exact RIMG1
       | |- rng _ _ 4096 => first [exact RCTX1 | exact RT1]
       | |- rng _ _ 32 => eapply rng_sub'; [exact RMB1|]; clear -MS4; lia
       | |- rng _ _ _ => exact RSTK1
       | |- _ \/ _ => first [unboxed DMT | unboxed DMC]
       | |- forall _, _ => idtac
       | |- ablk _ _ => exact MLO | |- iclr _ _ => assumption   (* [comment removed for export] *)
       | |- _ => unfold AIMG_HI; clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 MPOS MSAL MCE CX0 CX1 T0 T1 RA CXI TIC CBND TBND; lia
       end.
  (* [comment removed for export] *)
  all: intros rsp RNG' m' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 HF MUu MIu STu SJu.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF |].
  all: unfold sdealloc_post, sdealloc_W, sdealloc_tail_W in *.
  all: split; [ eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_weaken; [| exact MUu]];
                let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia |].
  all: split; [exact MIu|]. all: split; [exact STu|].
  all: split; [eapply cells_frameD; [exact NSC | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply cells_frameD; [exact SRT | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply junk_frameD; [eapply junk_of_cells'; [exact JS4| reflexivity] | exact MUu | intros _; cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply cells_frameD; [exact MTX | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply junk_frameD; [eapply junk_of_cells'; [exact GL2| reflexivity] | exact MUu | intros _; cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply u64arr_frameD; [exact ARR | exact MUu | rewrite ?upd_length, ?length_map; cbn; ub DMP; ub DPT; clear -CEIL LO SPR PA0 PL1 PL2 PL3 PA1 IDX NSR LEN Y Y0 NRB PBND; lia]|].
  all: split; [first [ intros NE; exfalso; exact (NE EQI)
                     | intros _; eapply cells_frameD; [exact LH | exact MUu | cbn; ub LDM; ub LDT; clear -CEIL LO SPR LCE Y Y0; lia] ]|].
  all: split; [exact SJu|].
  all: eapply cells_frameD; [exact SHZ | exact MUu | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -CEIL LO SPR SHR MLO ML1 ML2 ML3 T0 TIC MBND ASD MS4 TBND; lia].
Qed.

End CANSEC2.
