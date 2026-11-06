From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* The instruction runs of the ubsan gestures_end (0x13200, 32-byte frame). Each ubsan check branches to the trap at
   0x132d4 (unimp); every such branch is shown not taken from the premises. *)

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts.
  rewrite !bv_signed_small by (rewrite unsigned_lit; lia). rewrite !unsigned_lit by lia. reflexivity.
Qed.

(* A trap branch shown not taken. *)
Ltac gs_nt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [cbv iota
      | symmetry;
        first [ solve [unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
              | solve [vm_compute; reflexivity] ] ]
  end.

Ltac gs_cmp :=
  repeat match goal with
  | |- context [v_sltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      first
        [ replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 1)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 0)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  | |- context [v_sltiu (Z_to_bv 64 ?x) 1] =>
      first
        [ replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 1)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 0)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  end.

Ltac gs_land :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] =>
      replace (Z.land (bv_unsigned (Z_to_bv 64 x)) 7) with 0
        by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia;
            Z.div_mod_to_equations; lia)
  end.

(* s->held[i]'s checked load (0x13234-0x13260 and 0x13268-0x13294): HP + 8 i does not wrap, is not NULL and is
   8-aligned. *)
Ltac gs_elem := step; step; step; gs_nt; step; gs_cmp; step; gs_cmp; step; step; gs_nt; step; gs_nt;
  step; step; gs_land; step; gs_nt; step.

Lemma ge_segP : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA HP NH : Z) (j0 j1 j2 j3 : list byte),
  length j0 = 8%nat -> length j1 = 8%nat -> length j2 = 8%nat -> length j3 = 8%nat ->
  rw_cells rsegs m (bv_unsigned sp + -32) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)] ->
  SA + 52 <= bv_unsigned sp + -32 -> 0 < SA -> SA mod 8 = 0 -> 32 <= bv_unsigned sp -> 0 <= NH < 2 ^ 31 ->
  evt rsegs (fun ms => exists a0' m',
      ((NH = 0 /\ ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 SA) s1 a0'
                             a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x132ac) fc None m' (seg_rom rsegs)) \/
       (0 < NH /\ ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 SA) (Z_to_bv 64 0) a0'
                             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13234) fc None m' (seg_rom rsegs))) /\
      munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
      rw_cells rsegs m' (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13200) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SA HP NH
    j0 j1 j2 j3 L0 L1 L2 L3 FR HS DJ SA0 SA8 SP32 NHB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize] in HSB.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step.
  step. gs_nt.
  step. step. gs_land. step. gs_nt.
  step.
  rewrite (sx32_small NH) by lia.
  step.
  rewrite (lts_small 0 NH) by lia.
  destruct (0 <? NH) eqn:HC; cbn [negb]; cbv iota.
  - apply Z.ltb_lt in HC. step. step.
    apply evt_done. do 2 eexists. split; [right; split; [exact HC | reflexivity]|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - apply Z.ltb_ge in HC.
    apply evt_done. do 2 eexists. split; [left; split; [lia | reflexivity]|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma ge_segG : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA HP NH i a : Z),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (HP + 8 * i)) 8 = Some (le8 (Z_to_bv 64 a)) ->
  0 <= SA -> 0 < HP -> HP mod 8 = 0 -> 0 <= i -> HP + 8 * i + 8 <= 2 ^ 64 ->
  evt rsegs (fun ms => exists a1' a2' a3',
                 ms = MS (mkR (Z_to_bv 64 0x13268) sp gp tp t0 t1 t2 (Z_to_bv 64 SA) (Z_to_bv 64 (8 * i))
                            (Z_to_bv 64 a) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x14d1c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SA) (Z_to_bv 64 (8 * i)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13234) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SA HP NH i a
    HS HR SA0 HP0 HP8 I0 HB.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize] in HSB.
  gs_elem. step.
  apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma ge_segF : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA HP NH i a : Z),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (HP + 8 * i)) 8 = Some (le8 (Z_to_bv 64 a)) ->
  0 <= SA -> 0 < HP -> HP mod 8 = 0 -> 0 <= i -> HP + 8 * i + 8 <= 2 ^ 64 ->
  evt rsegs (fun ms => exists a1' a2' a3',
                 ms = MS (mkR (Z_to_bv 64 0x1329c) sp gp tp t0 t1 t2 (Z_to_bv 64 SA) (Z_to_bv 64 (8 * i))
                            (Z_to_bv 64 a) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x15f4c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SA) (Z_to_bv 64 (8 * i)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13268) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SA HP NH i a
    HS HR SA0 HP0 HP8 I0 HB.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize] in HSB.
  gs_elem. step.
  apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma ge_segT : forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA HP NH : Z),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)] ->
  0 <= SA ->
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x132b4) sp gp tp t0 t1 t2 (Z_to_bv 64 SA) s1
                                 (Z_to_bv 64 HP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x15f4c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SA) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x132ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SA HP NH
    HS SA0.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize] in HSB.
  step. step.
  apply evt_done. reflexivity.
Qed.

Lemma ge_segN : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA HP NH i : Z),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)] ->
  0 <= SA -> 0 <= i < NH -> NH < 2 ^ 31 - 1 ->
  evt rsegs (fun ms => exists a0',
      (i + 1 < NH /\ ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SA) (Z_to_bv 64 (8 * (i + 1))) a0' a1 a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 (i + 1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x13234) fc None m (seg_rom rsegs)) \/
      (i + 1 = NH /\ ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SA) (Z_to_bv 64 (8 * (i + 1))) a0' a1 a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 (i + 1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x132ac) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SA) (Z_to_bv 64 (8 * i)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 i) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1329c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SA HP NH i
    HS SA0 IB NHB.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize] in HSB.
  step. step. step.
  rewrite (sx32_small NH) by lia.
  step.
  rewrite (lts_small (i + 1) NH) by lia.
  replace (8 * i + 8) with (8 * (i + 1)) by lia.
  destruct (i + 1 <? NH) eqn:HC; cbv iota.
  - apply Z.ltb_lt in HC. apply evt_done. eexists. left. split; [exact HC | reflexivity].
  - apply Z.ltb_ge in HC. apply evt_done. eexists. right. split; [lia | reflexivity].
Qed.

Lemma ge_segE : forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S SA : Z) (hp nh ra0 w8 w9 w18 : word),
  rw_cells rsegs m (S + -32) [C8 w18; C8 w9; C8 w8; C8 ra0] ->
  rw_cells rsegs m (SA + 40) [C8 hp; C4 nh] ->
  SA + 52 <= S + -32 -> 0 <= SA -> 32 <= S < 2 ^ 64 ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 w8 w9 a0 a1 a2 a3 a4 a5 a6 a7
                   w18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      munch [(SA + 40, SA + 52)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (SA + 40) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' (S + -32) [C8 w18; C8 w9; C8 w8; C8 ra0])
    (MS (mkR ra (Z_to_bv 64 (S + -32)) gp tp t0 t1 t2 (Z_to_bv 64 SA) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x132b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S SA
    hp nh ra0 w8 w9 w18 FR HS DJ SA0 SB.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize] in HSB.
  pose proof (munch_refl [(SA + 40, SA + 52)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step. step. step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|].
  split; [|eassumption].
  eassumption.
Qed.
