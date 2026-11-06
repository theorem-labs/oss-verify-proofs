(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
     image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
       sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
     source runs: lib/B/Prog/Seg/F15.v (not in this delivery) seg_F15 (the sl_run run) and seg_F15b (the sl_run
       run) at a working branch 3803efccea0
       (blob e480181ea080a727bb5059e3030fd8bbb55aa9db).  Neither stretch calls, so there is no _pre_F / _post_F
       split; neither stores, and neither reads a shadow byte (no instrumented check in 0x82378-0x823d8);
     tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
           lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
     compare: seg_F15_run / seg_F15b_run re-derive the run the segment proof feeds to Tac_slot.sl_run_lib, from
       seg_F15_F / seg_F15b_F at RNG := RNG_all (evtF_evt, every rng premise by rng_all).  The segment proof itself
       states its run in the UL engine and lifts it with SmLib.ul_entry; the lib.Lib form below is the one
       Tac_slot.sl_run_lib takes (F7.v's path). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* The read facts in the `ov_read_bytes _ _ (wa a) 8 = Some bs` form StepF's `step` consumes (F15.v's rd8, over
   the lib.Lib Mem of this engine). *)
Lemma f15f_rd8 : forall (m : word -> option byte) (a v : Z),
  Mem.bytes_at rsegs m a (le8 (Z_to_bv 64 v)) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H.
  pose proof (Mem.bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH.
  rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite length_le8; lia).
  exact HH.
Qed.

(* The one arithmetic step `step` leaves folded (F15.v's f15_sub_val). *)
Lemma f15f_sub_val : forall x y v, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v = x - y ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - bv_unsigned (Z_to_bv 64 y)) = Z_to_bv 64 v.
Proof. intros x y v Hx Hy ->. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Ltac f15f_sub v :=
  match goal with
  | |- context [Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ?x) - bv_unsigned (Z_to_bv 64 ?y))] =>
      rewrite (f15f_sub_val x y v) by lia
  end.


(* The lib.Lib `solve_cond` folds only literal operands (Step.v fold_lit_ux is guarded by is_Zlit), and every
   compare of this stretch has one operand that is a carried value (pl, q, pll, r).  Same base tactics, with
   `bv_unsigned (Z_to_bv 64 z) = z` for a carried z in front. *)
Ltac f15f_base :=
  first [ reflexivity
        | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Z.leb_le; lia | apply Z.leb_gt; lia
        | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ].
Ltac f15f_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); f15f_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); f15f_rec
  | _ => f15f_base
  end.
Ltac f15f_cond :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  fold_lit_ux; repeat (rewrite MState.unsigned_lit by lia); f15f_rec.
Ltac fif_true :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; f15f_cond]
  end.
Ltac fif_false :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; f15f_cond]
  end.
Ltac bvlit := first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].

(* ===== S_F15: 0x82378 -> 0x8237c.  `bnez a0,82fa4` with a0 = 0: not taken.  No memory access at all. ===== *)

Lemma seg_F15_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v
                               s10 s11v t3 t4 t5 t6)
                          Fr (Z_to_bv 64 0x8237c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82378) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6
    Fr fc m ->.
  step. if_false.
  apply evtF_done. cbv beta. first [reflexivity | (f_equal; bvlit)].
Qed.

(* ===== S_F15b: 0x8237c -> 0x823d8 (the turn closes a record, r = 1) or 0x82468 (r <> 1).
   r  = s7 = fg_ret of the fragment class of the turn, s6 = 1, s11 = -8;
   q  = [A+256] = fragb fr + 8, pl = [A+128] = q + 11 = fragb fr + 19,
   pp = [A+304] = fr + 272 with [pp] = pl, pn = [A+296] = fr + 304 with [pn] = pll = f_pll.
   The six 8-byte reads are the whole memory footprint; no store, no shadow byte. ===== *)

Lemma seg_F15b_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q pl pp pn pll r : Z),
    s1v = Z_to_bv 64 A -> s6v = Z_to_bv 64 1 -> s7v = Z_to_bv 64 r -> s11v = Z_to_bv 64 (-8) ->
    0 <= r <= 1 ->
    0 <= A -> A + 312 <= 2 ^ 64 ->
    0 <= q -> q + 12 <= 2 ^ 64 -> pl = q + 11 ->
    Mem.bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 pl)) ->
    Mem.bytes_at rsegs m (A + 256) (le8 (Z_to_bv 64 q)) ->
    Mem.bytes_at rsegs m (A + 304) (le8 (Z_to_bv 64 pp)) ->
    Mem.bytes_at rsegs m (A + 296) (le8 (Z_to_bv 64 pn)) ->
    (r = 1 -> 0 <= pp /\ pp + 8 <= 2 ^ 64 /\ Mem.bytes_at rsegs m pp (le8 (Z_to_bv 64 pl))) ->
    (r = 1 -> 0 <= pn /\ pn + 8 <= 2 ^ 64 /\ Mem.bytes_at rsegs m pn (le8 (Z_to_bv 64 pll))) ->
    (r = 1 -> 1 <= pll <= 51) ->
    rng RNG (A + 128) 8 -> rng RNG (A + 256) 8 -> rng RNG (A + 296) 8 -> rng RNG (A + 304) 8 ->
    (r = 1 -> rng RNG pp 8) -> (r = 1 -> rng RNG pn 8) ->
    evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' pc' : word),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' a1' a2' a3' a4' a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v
                       s10 s11v t3 t4 t5 t6)
                  Fr pc' fc None m (seg_rom rsegs) /\
         ((pc' = Z_to_bv 64 0x823d8 /\ r = 1 /\ a1' = Z_to_bv 64 (pll + 5)) \/
          (pc' = Z_to_bv 64 0x82468 /\ r <> 1)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8237c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6
    Fr fc m A q pl pp pn pll r -> -> -> -> Hr HA0 HA1 Hq0 Hq1 Epl H128 H256 H304 H296 Hpp Hpn Hpll
    G128 G256 G296 G304 Gpp Gpn.
  pose proof (f15f_rd8 m _ _ H128) as RD128.
  pose proof (f15f_rd8 m _ _ H256) as RD256.
  pose proof (f15f_rd8 m _ _ H304) as RD304.
  pose proof (f15f_rd8 m _ _ H296) as RD296.
  (* 0x8237c bne s7,s6 (s6 = 1) *)
  step.
  destruct (Z.eq_dec r 1) as [Hc|Hn].
  - (* the turn closes a record: the four record checks and the two arithmetic checks all pass *)
    rewrite Hc. if_false.
    destruct (Hpp Hc) as (Hpp0 & Hpp1 & Bpp). destruct (Hpn Hc) as (Hpn0 & Hpn1 & Bpn).
    specialize (Hpll Hc). specialize (Gpp Hc). specialize (Gpn Hc).
    pose proof (f15f_rd8 m _ _ Bpp) as RDpp.
    pose proof (f15f_rd8 m _ _ Bpn) as RDpn.
    assert (RDpp0 : ov_read_bytes rsegs m (wa (pp + 0)) 8 = Some (le8 (Z_to_bv 64 pl)))
      by (rewrite Z.add_0_r; exact RDpp).
    assert (RDpn0 : ov_read_bytes rsegs m (wa (pn + 0)) 8 = Some (le8 (Z_to_bv 64 pll)))
      by (rewrite Z.add_0_r; exact RDpn).
    assert (UL2 : bv_unsigned (Z_to_bv 64 (pll + 2)) = pll + 2) by (apply MState.unsigned_lit; lia).
    (* 0x82380 ld a0,304(s1) ; 0x82384 ld a0,0(a0) ; 0x82388 ld a1,256(s1) *)
    step. step. step.
    (* 0x8238c bltu a0,a1: pl = q + 11, not taken *)
    step. fif_false.
    (* 0x82390 ld a1,256(s1) ; 0x82394 sub a2,a0,a1 = 11 *)
    step. step. f15f_sub 11.
    (* 0x82398 li a1,64 ; 0x8239c bltu a1,a2: 64 < 11 false *)
    step. step. fif_false.
    (* 0x823a0 ld a1,296(s1) ; 0x823a4 ld a1,0(a1) ; 0x823a8 addi a3,a1,2 ; 0x823ac li a4,64 *)
    step. step. step. step.
    (* 0x823b0 sub a2,a4,a2 = 53 *)
    step.
    (* 0x823b4 bltu a2,a3: 53 < pll + 2 false (pll <= 51) *)
    step. fif_false.
    (* 0x823b8 ld a2,256(s1) ; 0x823bc li a3,-12 ; 0x823c0 bltu a3,a2: the arithmetic check, not taken *)
    step. step. step. fif_false.
    (* 0x823c4 ld a2,128(s1) ; 0x823c8 bne a0,a2: pl = [A+128], not taken *)
    step. step. fif_false.
    (* 0x823cc ld a0,256(s1) ; 0x823d0 bltu s11,a0: the second arithmetic check, not taken *)
    step. step. fif_false.
    (* 0x823d4 addi a1,a1,5 *)
    step.
    repeat (rewrite MState.unsigned_lit by lia).
    apply evtF_done. cbv beta. do 6 eexists.
    split; [first [reflexivity | (cbv delta [mkR]; reflexivity)]|].
    left. split; [bvlit|]. split; [first [exact Hc | reflexivity]|].
    first [reflexivity | bvlit | (repeat (rewrite MState.unsigned_lit by lia); bvlit)].
  - (* the turn does not close a record: the branch at 0x8237c is taken, landing at 0x82468 *)
    fif_true.
    apply evtF_done. cbv beta. do 6 eexists.
    split; [first [reflexivity | (cbv delta [mkR]; reflexivity)]|].
    right. split; [bvlit | exact Hn].
Qed.

(* ===== The runs themselves, in the lib.Lib Exec form Tac_slot.sl_run_lib takes (the auditor's compare: the
   footprint twins at RNG := RNG_all, every rng premise by rng_all). ===== *)

Lemma seg_F15_run :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    Exec.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v
                               s10 s11v t3 t4 t5 t6)
                          Fr (Z_to_bv 64 0x8237c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82378) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6
    Fr fc m Ha0.
  apply (evtF_evt rsegs RNG_all). apply seg_F15_F. exact Ha0.
Qed.

Lemma seg_F15b_run :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q pl pp pn pll r : Z),
    s1v = Z_to_bv 64 A -> s6v = Z_to_bv 64 1 -> s7v = Z_to_bv 64 r -> s11v = Z_to_bv 64 (-8) ->
    0 <= r <= 1 ->
    0 <= A -> A + 312 <= 2 ^ 64 ->
    0 <= q -> q + 12 <= 2 ^ 64 -> pl = q + 11 ->
    Mem.bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 pl)) ->
    Mem.bytes_at rsegs m (A + 256) (le8 (Z_to_bv 64 q)) ->
    Mem.bytes_at rsegs m (A + 304) (le8 (Z_to_bv 64 pp)) ->
    Mem.bytes_at rsegs m (A + 296) (le8 (Z_to_bv 64 pn)) ->
    (r = 1 -> 0 <= pp /\ pp + 8 <= 2 ^ 64 /\ Mem.bytes_at rsegs m pp (le8 (Z_to_bv 64 pl))) ->
    (r = 1 -> 0 <= pn /\ pn + 8 <= 2 ^ 64 /\ Mem.bytes_at rsegs m pn (le8 (Z_to_bv 64 pll))) ->
    (r = 1 -> 1 <= pll <= 51) ->
    Exec.evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' pc' : word),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' a1' a2' a3' a4' a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v
                       s10 s11v t3 t4 t5 t6)
                  Fr pc' fc None m (seg_rom rsegs) /\
         ((pc' = Z_to_bv 64 0x823d8 /\ r = 1 /\ a1' = Z_to_bv 64 (pll + 5)) \/
          (pc' = Z_to_bv 64 0x82468 /\ r <> 1)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8237c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5v s6v s7v s8 s9v s10 s11v t3 t4 t5 t6
    Fr fc m A q pl pp pn pll r E1 E6 E7 E11 Hr HA0 HA1 Hq0 Hq1 Epl H128 H256 H304 H296 Hpp Hpn Hpll.
  apply (evtF_evt rsegs RNG_all).
  eapply (seg_F15b_F RNG_all); try eassumption.
  all: try (apply rng_all; lia).
  all: intro Hc; destruct (Hpp Hc) as (Xp & Yp & _); destruct (Hpn Hc) as (Xn & Yn & _);
       apply rng_all; lia.
Qed.
