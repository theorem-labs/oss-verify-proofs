(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition lm_spill (X f Y zlen : Z) (w16 : word) (j128 j136 : list byte) : list cell :=
  [C8 w16; C8 (Z_to_bv 64 (f / 8 + 2147450956)); C8 (Z_to_bv 64 (8 * zlen)); C8 (Z_to_bv 64 (f + 608)); C8 (Z_to_bv 64 (Z.shiftl zlen 48)); C8 (Z_to_bv 64 5);
   C8 (Z_to_bv 64 Y); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 zlen); C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 ((X + 496) / 8 + 2147450880));
   C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 X); CB 8 j128; CB 8 j136; C8 (Z_to_bv 64 f)].

Definition lm_WL (X spq f : Z) : list (Z * Z) :=
  [(spq + 16, spq + 152); (f + 528, f + 530); (f + 608, f + 1106); (f / 8 + 2147450956, f / 8 + 2147451019); (X, X + 504)].

Definition lm_inv (X spq f Y : Z) (ybs : list byte) (m0 : mem) (ziw : word) (zsh : list byte) (mm : mem) (xlen zlen : Z) : Prop :=
  (exists w16 j128 j136, rw_cells asegs mm (spq + 16) (lm_spill X f Y zlen w16 j128 j136)) /\
  (exists xbs, u8arr asegs mm X xbs /\ length xbs = 496%nat) /\
  rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] /\ 0 <= xlen <= 62 /\ 0 <= zlen <= 62 /\
  bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  (exists zibs, u8arr asegs mm (f + 608) zibs /\ length zibs = 496%nat) /\
  rw_cells asegs mm (f + 1104) [C2 ziw] /\
  rw_cells asegs mm (f / 8 + 2147450956) [CB 63 zsh] /\
  bytes_at asegs mm Y ybs /\
  mem_inv asegs mm /\ munch (lm_WL X spq f) m0 mm /\ wmono asegs m0 mm.

Definition lm_xinv (X spq f : Z) (m0 : mem) (mm : mem) : Prop :=
  (exists ja0 ja1, rw_cells asegs mm (spq + 16) [CB 56 ja0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 64 ja1]) /\
  (exists xbs, u8arr asegs mm X xbs /\ length xbs = 496%nat) /\
  (exists xlen, rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] /\ 0 <= xlen <= 62) /\
  bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  mem_inv asegs mm /\ munch (lm_WL X spq f) m0 mm /\ wmono asegs m0 mm.

Lemma lm_spill_exit : forall (m : mem) A c1 c2 c3 c4 c5 c6 c7 v1 v2 c10 c11 c12 c13 c14 c15 c16 c17,
  rw_cells asegs m A [c1; c2; c3; c4; c5; c6; c7; C8 v1; C8 v2; c10; c11; c12; c13; c14; c15; c16; c17] ->
  cells_size [c1; c2; c3; c4; c5; c6; c7] = 56%nat -> cells_size [c10; c11; c12; c13; c14; c15; c16; c17] = 64%nat ->
  exists ja0 ja1, rw_cells asegs m A [CB 56 ja0; C8 v1; C8 v2; CB 64 ja1].
Proof.
  intros m A c1 c2 c3 c4 c5 c6 c7 v1 v2 c10 c11 c12 c13 c14 c15 c16 c17 H S1 S2.
  pose proof (rw_cells_merge asegs m A [] [c1; c2; c3; c4; c5; c6; c7] [C8 v1; C8 v2; c10; c11; c12; c13; c14; c15; c16; c17] H) as H1.
  rewrite S1 in H1. cbn [app] in H1.
  pose proof (rw_cells_merge asegs m A [CB 56 (cells_bytes [c1; c2; c3; c4; c5; c6; c7]); C8 v1; C8 v2] [c10; c11; c12; c13; c14; c15; c16; c17] []) as H2.
  rewrite app_nil_r in H2. specialize (H2 H1). rewrite S2 in H2. cbn [app] in H2.
  eexists _, _. exact H2.
Qed.

Ltac lm_xclose :=
  lazymatch goal with
  | |- lm_xinv _ _ _ _ _ =>
      unfold lm_xinv, lm_WL;
      split; [lazymatch goal with SP : rw_cells asegs _ (_ + 16)%Z _ |- _ => exact (lm_spill_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP eq_refl eq_refl) end|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac lm_open H :=
  let w16 := fresh "w16" in let j128 := fresh "j128" in let j136 := fresh "j136" in let xbs := fresh "xbs" in let zibs := fresh "zibs" in
  destruct H as ((w16 & j128 & j136 & SPILL) & (xbs & XA & XL) & XN & ?LEN & ?ZLN & ZR & (zibs & ZIA & ZIL) & ZIC & ZSH & YB & MI & MU & WM);
  unfold lm_spill in SPILL; unfold lm_WL in MU.
Ltac lm_forget := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
  | H : length _ = 496%nat |- _ => clear H | H : length _ = length _ |- _ => clear H end.
Ltac lm_close :=
  lazymatch goal with
  | |- lm_inv _ _ _ _ _ _ _ _ _ _ _ =>
      unfold lm_inv, lm_spill, lm_WL;
      split; [do 3 eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [lia|]; split; [lia|]; split; [eassumption|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Section LMK.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X spq f Y : Z) (ybs : list byte) (m0 : mem).
  Variable Q : machine_state -> Prop.
  Notation LMINV := (lm_inv X spq f Y ybs m0).
  Notation LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (f / 8 + 2147450880)) xs4 xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition lm_head_k (idx0 : Z) : Prop :=
    forall (idx xlen zlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 ziw zsh (mm : mem),
      LMINV ziw zsh mm xlen zlen -> 1 <= idx < 5 /\ idx0 <= idx ->
      evt asegs Q (LMS 0xe90b0 (Z_to_bv 64 xlen) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 Y) (Z_to_bv 64 (1 - idx))
                       (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) (Z_to_bv 64 5) (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mm).

  Definition lm_exit_k : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 (mm : mem),
      lm_xinv X spq f m0 mm ->
      evt asegs Q (LMS 0xe97d0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm).

  Definition lm_cpy2_k (idx0 : Z) : Prop :=
    forall (idx xlen zlen : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 (mm : mem),
      LMINV (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 63) mm xlen zlen -> 1 <= idx < 5 /\ idx0 <= idx + 1 ->
      evt asegs Q (LMS 0x812f8 (Z_to_bv 64 0xe91ec) xt0 xt1 xt2 (Z_to_bv 64 (f + 608)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (8 * zlen)) xa3 xa4 xa5 xa6 xa7 xs2
                       (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 xlen) (Z_to_bv 64 (1 - idx))
                       (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) (Z_to_bv 64 5) (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mm).

  Definition lm_mset_k (idx0 : Z) : Prop :=
    forall (idx xlen zlen k : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 ziw (mm : mem),
      LMINV ziw (repeat (Z_to_bv 8 0) 63) mm xlen zlen -> 1 <= idx < 5 /\ idx0 <= idx + 1 -> 0 <= k -> xlen < idx + k <= 62 ->
      evt asegs Q (LMS 0x81794 (Z_to_bv 64 0xe92f4) xt0 xt1 xt2 (Z_to_bv 64 (X + 8 * xlen)) (Z_to_bv 64 0) (Z_to_bv 64 (8 * (idx + k - xlen))) xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 (idx + k)) (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 (Z.shiftl k 48)) (Z_to_bv 64 (1 - idx))
                       (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) (Z_to_bv 64 k) (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mm).
End LMK.
