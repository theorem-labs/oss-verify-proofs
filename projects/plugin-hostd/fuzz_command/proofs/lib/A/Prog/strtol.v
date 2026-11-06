(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and module names changed; 71 of its 98 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Spec Require Import CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import __shlim_c __intscan_c strtol_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. unfold ro_cells, cells_at. split; [split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma rwc_split : forall segs m A B cs1 cs2, rw_cells segs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells segs m A cs1 /\ rw_cells segs m B cs2.
Proof.
  intros segs m A B cs1 cs2 [[Hwf Hb] (H0 & H1 & H2)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in H1, H2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H2. lia.
Qed.

Lemma rwc_join : forall segs m A B cs1 cs2, rw_cells segs m A cs1 -> rw_cells segs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A B cs1 cs2 [[W1 B1] (H0 & H1 & H2)] [[W2 B2] (G0 & G1 & G2)] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - unfold wr_at. rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply H2. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G2. lia.
Qed.

Ltac ntk := let K := fresh "K" in if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia | clear K].
Ltac jn H1 H2 :=
  let J := fresh "J" in
  pose proof (rwc_join _ _ _ _ _ _ H1 H2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J;
  clear H1 H2; cbn [app] in J; rename J into H1.

Theorem strtol_holds : __shlim_contract -> __intscan_contract -> strtol_contract.
Proof.
  intros SHL ISC. unfold strtol_contract, STRTOL, STRTOL_SSP_GOT, STRTOL_SSP_GUARD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Ep str ev can e0 lo
    BY HP EP0 EC ER GOT GD ST HLO D1 D2 D3 D4 D5 D6 D7 D8 MI.
  pose proof (bytes_at_bound _ _ _ _ BY) as B1. rewrite length_app in B1. cbn [length] in B1.
  pose proof (rw_cells_bound _ _ _ _ EC) as B2. pose proof (rw_cells_bound _ _ _ _ ER) as B3.
  cbn [cells_size csize Nat.add] in B2, B3.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  apply ro8 in GOT. apply ro8 in GD.
  pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp); (Ep, Ep + 8);
              (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 288%nat ST.
  do 20 zstep.
  pose proof (rwc_split _ _ _ (bv_unsigned sp + -288 + 8) [_] _ FR) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). destruct X as [F0 R].
  pose proof (rwc_split _ _ _ (bv_unsigned sp + -288 + 24) [_; _] _ R) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). clear R. destruct X as [F1 R].
  pose proof (rwc_split _ _ _ (bv_unsigned sp + -288 + 88) [_] _ R) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). clear R. destruct X as [F2 R].
  pose proof (rwc_split _ _ _ (bv_unsigned sp + -288 + 96) [_] _ R) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). clear R. destruct X as [F3 R].
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [88%nat; 24%nat; 24%nat]) in R; [| reflexivity].
  cbn [mk_CB_cells app] in R.
  pose proof (rwc_split _ _ _ (bv_unsigned sp + -288 + 184) [_] _ R) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). clear R. destruct X as [F4 R].
  pose proof (rwc_split _ _ _ (bv_unsigned sp + -288 + 208) [_] _ R) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). clear R. destruct X as [F5 R].
  pose proof (rwc_split _ _ _ (bv_unsigned sp + -288 + 232) [_] _ R) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). clear R. destruct X as [F6 F7].
  call SHL; [exact F1 | exact F3 | exact F5 | exact MI | ].
  match goal with H : rw_cells _ _ (bv_unsigned sp + -288 + 184) _ |- _ =>
    rewrite unsigned_lit in H by lia; rewrite Z.sub_diag in H; rename H into F5 end.
  do 5 zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply ISC | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold __intscan_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call segs mm ]
  end;
  [ exact F1 | exact F3 | exact F5 | exact BY | exact HP | exact ER
  | rewrite unsigned_lit by lia; exact ST
  | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
  | rewrite unsigned_lit by lia; lia | lia | lia | assumption | ].
  match goal with H : rw_cells _ _ (bv_unsigned sp + -288 + 8) _ |- _ => rename H into G1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -288 + 184) _ |- _ => rename H into G5 end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
  jn F6 F7. jn G5 F6. jn F4 G5. jn F3 F4. jn F2 F3. jn G1 F2. jn F0 G1.
  zstep. ntk. do 7 zstep.
  zstep. zstep. zstep. ntk.
  do 7 zstep.
  release_frame F0 ST (bv_unsigned sp).
  zstep.
  match goal with H : rw_cells _ _ Ep [C8 ?w] |- _ => replace w with (Z_to_bv 64 (A + s10_end str)) in H by word_eq_tac end.
  finish.
Qed.
