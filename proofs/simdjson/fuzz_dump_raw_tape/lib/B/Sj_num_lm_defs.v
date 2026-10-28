(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit Sj_num_bkit Sj_num_bdefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition lm_spillB (X f : Z) (a0 a8 a16 a24 a56 a72 a96 a104 : list byte) : list cell :=
  [CB 8 a0; CB 8 a8; CB 8 a16; CB 8 a24; C8 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)); C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f);
   CB 8 a56; C8 (Z_to_bv 64 f); CB 8 a72; C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 5); CB 8 a96; CB 8 a104; C8 (Z_to_bv 64 f)].

Definition lm_spillL (X f zl : Z) (a0 a96 a104 : list byte) : list cell :=
  [CB 8 a0; C8 (Z_to_bv 64 (18446744073709551615 - (f + 32))); C8 (Z_to_bv 64 (18446744073709551615 - (f + 608))); C8 (Z_to_bv 64 (Z.shiftl zl 48));
   C8 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)); C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f);
   C8 (Z_to_bv 64 zl); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (8 * zl)); C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 5); CB 8 a96; CB 8 a104; C8 (Z_to_bv 64 f)].

Definition lm_WL (X spq f : Z) : list (Z * Z) :=
  [(spq - 80, spq + 120); (f + 528, f + 530); (f + 608, f + 1106); (f / 8 + 2147450956, f / 8 + 2147451019); (X, X + 504)].

Definition lm_inv (X spq f lo : Z) (ybs : list byte) (m0 : mem) (spl : list cell) (zsh : list byte) (ziw : word) (mm : mem) (len : Z) (P : Prop) : Prop :=
  rw_cells bsegs mm spq spl /\
  (exists bs, u8arr bsegs mm X bs /\ length bs = 496%nat /\ (P -> bignorm_b bs len)) /\
  rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ 0 <= len <= 62 /\
  bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  (exists zibs, u8arr bsegs mm (f + 608) zibs /\ length zibs = 496%nat) /\
  rw_cells bsegs mm (f + 1104) [C2 ziw] /\
  rw_cells bsegs mm (f / 8 + 2147450956) [CB 63 zsh] /\
  bytes_at bsegs mm B_P5LARGE ybs /\
  mem_inv bsegs mm /\ munch (lm_WL X spq f) m0 mm /\ wmono bsegs m0 mm /\ stk bsegs mm lo spq.

Definition lm_xinv (X spq f lo : Z) (m0 : mem) (mm : mem) (len : Z) (P : Prop) : Prop :=
  (exists ja jb, rw_cells bsegs mm spq [CB 48 ja; C8 (Z_to_bv 64 f); CB 64 jb]) /\
  (exists bs, u8arr bsegs mm X bs /\ length bs = 496%nat /\ (P -> bignorm_b bs len)) /\
  rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ 0 <= len <= 62 /\
  bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  (exists zsh, rw_cells bsegs mm (f / 8 + 2147450956) [CB 63 zsh]) /\
  mem_inv bsegs mm /\ munch (lm_WL X spq f) m0 mm /\ wmono bsegs m0 mm /\ stk bsegs mm lo spq.

Lemma lm_spill_exit : forall (m : mem) A c1 c2 c3 c4 c5 c6 v c8 c9 c10 c11 c12 c13 c14 c15,
  rw_cells bsegs m A [c1; c2; c3; c4; c5; c6; C8 v; c8; c9; c10; c11; c12; c13; c14; c15] ->
  cells_size [c1; c2; c3; c4; c5; c6] = 48%nat -> cells_size [c8; c9; c10; c11; c12; c13; c14; c15] = 64%nat ->
  exists ja jb, rw_cells bsegs m A [CB 48 ja; C8 v; CB 64 jb].
Proof.
  intros m A c1 c2 c3 c4 c5 c6 v c8 c9 c10 c11 c12 c13 c14 c15 H S1 S2.
  pose proof (rw_cells_merge bsegs m A [] [c1; c2; c3; c4; c5; c6] [C8 v; c8; c9; c10; c11; c12; c13; c14; c15] H) as H1.
  rewrite S1 in H1. cbn [app] in H1.
  pose proof (rw_cells_merge bsegs m A [CB 48 (cells_bytes [c1; c2; c3; c4; c5; c6]); C8 v] [c8; c9; c10; c11; c12; c13; c14; c15] []) as H2.
  rewrite app_nil_r in H2. specialize (H2 H1). rewrite S2 in H2. cbn [app] in H2.
  eexists _, _. exact H2.
Qed.

Ltac lm_open H :=
  let bs := fresh "bs" in let zibs := fresh "zibs" in
  destruct H as (SPILL & (bs & XA & ?XL & NB) & XN & ?LEN & ZR & (zibs & ZIA & ?ZIL) & ZIC & ZSH & YB & MI & MU & WM & ST);
  unfold lm_spillB, lm_spillL in SPILL; unfold lm_WL in MU.

Ltac lm_close_with nb :=
  lazymatch goal with
  | |- lm_inv _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold lm_inv, lm_spillB, lm_spillL, lm_WL;
      split; [eassumption|]; split; [eexists; split; [eassumption| split; [lia| nb]]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac lm_close := lm_close_with ltac:(let HF := fresh in intros HF; exact (False_ind _ HF)).
Ltac lm_xclose_with nb :=
  lazymatch goal with
  | |- lm_xinv _ _ _ _ _ _ _ _ =>
      unfold lm_xinv, lm_WL;
      split; [lazymatch goal with SP : rw_cells bsegs _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: nil) |- _ =>
                exact (lm_spill_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP eq_refl eq_refl) end|];
      split; [eexists; split; [eassumption| split; [lia| nb]]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|];
      split; [eexists; eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Section LMK.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo spq f len0 : Z) (ybs : list byte) (m0 : mem).
  Variable Q : machine_state -> Prop.
  Notation S := (f / 8 + 2147450880)%Z.
  Notation CAPL := (len0 + 6 <= 62)%Z.
  Notation zl := len0.
  Notation LMINV := (lm_inv X spq f lo ybs m0).
  Notation LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 S) (Z_to_bv 64 X) xs5 xs6
             (Z_to_bv 64 2147450880) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation LJ pc j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs11 xt3 xt4 xt5 xt6 mm :=
    (LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (-8)) (Z_to_bv 64 (8 * zl)) (Z_to_bv 64 18446744073709374047) xs8 (Z_to_bv 64 (f + 608)) (Z_to_bv 64 j) xs11
         xt3 xt4 xt5 xt6 mm).

  Definition lm_exit_k : Prop :=
    forall (r len : Z) (P : Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs5 xs6 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (mm : mem),
      lm_xinv X spq f lo m0 mm len P -> (CAPL -> P /\ r = 1 /\ len <= len0 + 6)%Z ->
      evt bsegs Q (LMS 0xedd6c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 f) xa6 xa7 xs2 xs5 xs6 (Z_to_bv 64 r) xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Definition lm_cpy2_k (j0 : Z) : Prop :=
    forall (j len : Z) xt0 xt2 xa3 xa4 xa5 xa6 xa7 w xt3 xt4 xt5 xt6 a0 a96 a104 (mm : mem),
      LMINV (lm_spillL X f zl a0 a96 a104) (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 0) mm len False -> (1 <= j < 5 /\ j0 <= j)%Z -> (CAPL -> len <= zl + j + 1)%Z ->
      evt bsegs Q (LJ 0x7ee9c j (Z_to_bv 64 0xed958) xt0 (Z_to_bv 64 5) xt2 (Z_to_bv 64 (f + 608)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (8 * zl)) xa3 xa4 xa5 xa6 xa7 w (Z_to_bv 64 B_P5LARGE)
                      xt3 xt4 xt5 xt6 mm).
End LMK.
