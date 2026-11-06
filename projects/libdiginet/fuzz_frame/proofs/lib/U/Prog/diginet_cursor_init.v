(* proves the UBSan contract of diginet_cursor_init (fuzz_frame.ubsan, 0x14170), with its alignment trap not taken. *)
(* Walk of diginet_cursor_init (src/diginet_msg.c:10-18 at 835f336c) in fuzz_frame.ubsan, 0x14170.
   The UBSan check at 0x14178 (c & 7 is not 0) branches to the trap at 0x1419c; the premise
   c mod 8 = 0 keeps it from firing. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import diginet_cursor_init_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.
(* The UBSan alignment check of a: the low 3 bits of the register value are 0. *)
Lemma al8 : forall x, x mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x H. rewrite unsigned_lit_wrap. change 7 with (Z.ones 3).
  rewrite Z.land_ones by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

(* Decide the branch to the alignment trap: not taken. *)
Ltac br_al H := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cd then _ else _) _ _ _ _) =>
      replace cd with false; [cbv iota | symmetry; unfold_cond; rewrite H; fold_lit_ux; reflexivity]
  end.

Theorem diginet_cursor_init_holds : diginet_cursor_init_contract.
Proof.
  unfold diginet_cursor_init_contract, DIGINET_CURSOR_INIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c body len cj
    Hc Hc8 Hb Hl CJ MI.
  pose proof (rw_cells_bound rsegs m c _ CJ) as CBd. cbn [cells_size csize Nat.add] in CBd.
  change (Z.of_nat 25) with 25 in CBd.
  pose proof (al8 c Hc8) as L7.
  pose proof (munch_refl [(c, c + 25)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x14170 beqz a0: c is not 0. *)
  step. br false.
  (* 0x14178 bnez (c & 7): the UBSan alignment trap, not taken. *)
  step. step. br_al L7.
  step. step. step.
  step. step. step. step.
  assert (L1 : le1 (Z_to_bv 64 0) = [b8 0]).
  { rewrite <- (le1_zxb (b8 0)). f_equal. }
  rewrite L1. mem_after_store.
  step.
  match type of CJ with context [C8 (Z_to_bv 64 (Z.land ?x ?y))] =>
    assert (A2 : Z_to_bv 64 (Z.land x y) = Z_to_bv 64 (if body =? 0 then 0 else len)) end.
  { unfold v_sltiu. rewrite (unsigned_lit body Hb), (unsigned_lit len Hl). change (bv_wrap 64 1) with 1.
    destruct (Z.eq_dec body 0) as [E|E].
    - subst body. rewrite Z.eqb_refl. change (0 <? 1) with true. cbv iota.
      match goal with |- context [Z.land ?x len] => replace x with 0 by (vm_compute; reflexivity) end.
      rewrite Z.land_0_l. reflexivity.
    - rewrite (proj2 (Z.eqb_neq _ _) E), (proj2 (Z.ltb_ge body 1)) by lia. cbv iota.
      match goal with |- context [Z.land ?x len] => replace x with (Z.ones 64) by (vm_compute; reflexivity) end.
      rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  rewrite A2 in CJ.
  apply evt_done.
  do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. unfold cursor_cells. exact CJ.
Qed.
