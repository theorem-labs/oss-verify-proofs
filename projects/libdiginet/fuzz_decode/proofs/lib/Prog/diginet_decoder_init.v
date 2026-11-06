(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Walk of diginet_decoder_init in fuzz_decode.plain (0x13e30, 20 instructions): beqz a0 (d is not 0);
   a 32-byte frame saves ra, s0, s1; jal diginet_cursor_init (0x13b10) on the cursor at d; when p is
   NULL (bnez s1 not taken), li a0, 1 and jal diginet_personality_of (0x13cc0); sd s1, 0x20(s0) stores
   the personality pointer; the frame is restored and the function returns. The callee contracts are
   the Section hypotheses CI and PO.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout
  diginet_cursor_init_c diginet_personality_of_c diginet_decoder_init_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- cell lists split and joined at a cell boundary ---- *)

Lemma rw_cells_split2 : forall m A cs1 cs2 (k : Z),
  Z.of_nat (cells_size cs1) = k ->
  rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + k) cs2.
Proof.
  intros m A cs1 cs2 k Hk [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite Hk in B2.
  rewrite cells_size_app in Hn.
  split.
  - split; [split; [exact W1 | exact B1]|].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hw. rewrite cells_size_app. lia.
  - split; [split; [exact W2 | exact B2]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + k + i) with (A + (k + i)) by lia. apply Hw. rewrite cells_size_app. lia.
Qed.

Lemma rw_cells_join2 : forall m A cs1 cs2 (k : Z),
  Z.of_nat (cells_size cs1) = k ->
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + k) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 k Hk [[W1 B1] (Ha1 & Hn1 & Hw1)] [[W2 B2] (Ha2 & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. rewrite Hk. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i k) as [L|L].
    + apply Hw1. lia.
    + replace (A + i) with (A + k + (i - k)) by lia. apply Hw2. lia.
Qed.

(* the stack stays writable and readable across a callee that writes only the cells it returns *)
Lemma stk_after : forall m m' lo hi A n cs,
  stk rsegs m lo hi -> munch [(A, A + n)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' A cs -> Z.of_nat (cells_size cs) = n -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi A n cs (H1 & H2 & H) MU WM [[Hwf (HA & HL & HB)] _] Hn.
  rewrite cells_bytes_length in HL by exact Hwf.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Z.ltb_spec a A) as [L|L]; [| destruct (Z.ltb_spec a (A + n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
  - assert (Hi : (Z.to_nat (a - A) < length (cells_bytes cs))%nat)
      by (rewrite cells_bytes_length by exact Hwf; lia).
    specialize (HB _ Hi). replace (A + Z.of_nat (Z.to_nat (a - A))) with a in HB by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) as [b'|] eqn:E.
    + exists b'. exact HB.
    + apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Section W.
Hypothesis CI : diginet_cursor_init_contract.
Hypothesis PO : diginet_personality_of_contract.

Theorem diginet_decoder_init_holds : diginet_decoder_init_contract.
Proof.
  unfold diginet_decoder_init_contract, DIGINET_DECODER_INIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    d body len lo p dj D0 B0 BR LR PR DJ ST LO DSP MI.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in SPR.
  pose proof (rw_cells_bound rsegs m d _ DJ) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof ST as (LO0 & _ & _).
  pose proof (rw_cells_split_CB rsegs m d [] 40 dj [] [25; 7; 8]%nat DJ eq_refl) as DS.
  cbn [app mk_CB_cells] in DS.
  destruct (rw_cells_split2 m d [CB 25 (firstn 25 dj)]
              [CB 7 (firstn 7 (skipn 25 dj)); CB 8 (firstn 8 (skipn 7 (skipn 25 dj)))] 25 eq_refl DS)
    as [DC DT].
  clear DS DJ.
  pose proof (munch_refl [(d, d + 40); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x13e30: beqz a0 *)
  step.
  if_cases K; zify_cond K; rewrite ?unsigned_lit, ?Z.mod_small in K by lia;
    try (exfalso; first [lia | congruence]).
  (* 0x13e34 .. 0x13e54: the frame, the moves, jal diginet_cursor_init *)
  carve_frame 32%nat ST.
  do 9 step.
  eapply evt_cut.
  { eapply CI with (a2 := Z_to_bv 64 0); [exact D0 | lia | lia | exact DC | exact MI]. }
  intros ms1 (a2' & a3' & m1 & -> & MU1 & WM1 & MI1 & CC).
  fix_ret.
  unfold cursor_cells in CC.
  replace (if body =? 0 then 0 else len) with len in CC
    by (destruct (Z.eqb_spec body 0); [contradiction | reflexivity]).
  pose proof (stk_after _ _ _ _ _ _ _ ST MU1 WM1 CC eq_refl) as ST1.
  pose proof (rw_cells_transport rsegs [(d, d + 25)] _ m1 (d + 25) _ DT MU1 WM1
    ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as DT1.
  pose proof (rw_cells_transport rsegs [(d, d + 25)] _ m1 (bv_unsigned sp + -32) _ FR MU1 WM1
    ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR1.
  lazymatch type of MU with
  | munch ?W ?m0 ?mc =>
      assert (MU2 : munch W m0 m1)
        by (apply (munch_trans W m0 mc m1 MU); apply (munch_weaken [(d, d + 25)] W mc m1);
            [ intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & Hx2 & _); split; [lia | exact I]
            | exact MU1 ])
  end.
  pose proof (wmono_trans rsegs _ _ _ WM WM1) as WM2.
  clear ST DT FR MU WM MI DC MU1 WM1.
  rename ST1 into ST, DT1 into DT, FR1 into FR, MU2 into MU, WM2 into WM, MI1 into MI.
  destruct p as [i|].
  - (* p = &personalities[i]: bnez s1 taken *)
    assert (PI : 0 <= i < 2) by (apply PR; reflexivity).
    assert (PV : personality_ptr (Some i) = 0x1d690 + 24 * i) by reflexivity.
    step.
    if_cases K2; zify_cond K2; rewrite ?PV in K2; rewrite ?unsigned_lit, ?Z.mod_small in K2 by lia;
      try (exfalso; first [lia | congruence]).
    do 6 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    unfold decoder_cells, cursor_cells.
    cbn [diginet_decoder_init dd_c dd_p dc_len dc_pos dc_status diginet_cursor_init].
    eapply (rw_cells_join2 _ _ _ _ 25); [reflexivity | exact CC | exact DT].
  - (* p = NULL: li a0, 1; jal diginet_personality_of *)
    change (personality_ptr None) with 0 in *.
    step.
    if_cases K2; zify_cond K2; rewrite ?unsigned_lit, ?Z.mod_small in K2 by lia;
      try (exfalso; first [lia | congruence]).
    do 2 step.
    eapply evt_cut.
    { eapply PO. lia. }
    intros ms2 (a1' & a2'' & ->).
    fix_ret.
    do 7 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    unfold decoder_cells, cursor_cells.
    cbn [diginet_decoder_init dd_c dd_p dc_len dc_pos dc_status diginet_cursor_init].
    eapply (rw_cells_join2 _ _ _ _ 25); [reflexivity | exact CC | exact DT].
Qed.

End W.
