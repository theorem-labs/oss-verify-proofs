From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition pkeep (R R0 : bvmap 5 word) : Prop :=
  forall r, r = 3 \/ r = 4 \/ 21 <= r <= 27 -> getr R (Z_to_bv 5 r) = getr R0 (Z_to_bv 5 r).

Ltac pk_tac :=
  unfold pkeep; let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in intros r Hr;
  assert (Hr' : r = 3 \/ r = 4 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; reflexivity.

Ltac pg_tac := first [ reflexivity |
  unfold getr;
  lazymatch goal with |- (if bv_eqb ?r ?z then _ else _) = _ =>
    let b := eval vm_compute in (bv_eqb r z) in change (bv_eqb r z) with b end;
  cbv iota; simp_regs; rewrite ?v_sltu_b2z; f_equal; rewrite ?unsigned_lit by lia; lia ].

Lemma ka_ps_ret : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m v res jv xra xs0 xs1 xs2 xs3 xs4,
  0 <= v -> v + 24 <= 2 ^ 64 -> s0 = Z_to_bv 64 v -> a0 = Z_to_bv 64 res -> 0 <= res < 2 ^ 64 ->
  bv_unsigned sp + 64 < 2 ^ 64 ->
  v + 24 <= bv_unsigned sp + 16 \/ bv_unsigned sp + 64 <= v + 16 ->
  rw_cells rsegs m (v + 16) [CB 8 jv] ->
  rw_cells rsegs m (bv_unsigned sp + 16) [C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  evt rsegs (fun ms => exists R m', ms = MS R F (ret_pc xra) fc None m' (seg_rom rsegs) /\
      getr R (Z_to_bv 5 1) = xra /\ getr R (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned sp + 64) /\
      getr R (Z_to_bv 5 8) = xs0 /\ getr R (Z_to_bv 5 9) = xs1 /\ getr R (Z_to_bv 5 18) = xs2 /\
      getr R (Z_to_bv 5 19) = xs3 /\ getr R (Z_to_bv 5 20) = xs4 /\
      getr R (Z_to_bv 5 10) = Z_to_bv 64 (if res =? 0 then -1 else 0) /\
      pkeep R (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) /\
      munch [(v + 16, v + 24)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (v + 16) [C8 (Z_to_bv 64 res)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x1459c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v res jv
    xra xs0 xs1 xs2 xs3 xs4 Hv Hv2 E0 E10 Hr Hsp HD VC FR. subst s0 a0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(v + 16, v + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 13 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [pg_tac|]. split; [pg_tac|]. split; [pg_tac|]. split; [pg_tac|]. split; [pg_tac|].
  split; [pg_tac|]. split; [pg_tac|].
  split.
  { unfold getr.
    lazymatch goal with |- (if bv_eqb ?r ?z then _ else _) = _ =>
      let b := eval vm_compute in (bv_eqb r z) in change (bv_eqb r z) with b end.
    cbv iota. simp_regs. rewrite ?v_sltu_b2z.
    rewrite (unsigned_lit 0), (unsigned_lit res) by lia.
    destruct (Z.eqb_spec res 0) as [->|Hn]; [reflexivity|].
    replace (0 <? res) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    rewrite (unsigned_lit 1) by lia. reflexivity. }
  split; [pk_tac|].
  split; [exact MU|]. split; [exact WM | exact VC].
Qed.
