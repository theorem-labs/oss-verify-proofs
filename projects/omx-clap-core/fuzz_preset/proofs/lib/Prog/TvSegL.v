From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import TvSeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import KindBGlue.
Import ListNotations.
Open Scope Z_scope.

Definition tv_lr0 (R : bvmap 5 word) (gp tp : word) (S t v d pretty : Z) : Prop :=
  getr R 2 = Z_to_bv 64 (S + -112) /\ getr R 3 = gp /\ getr R 4 = tp /\
  getr R 8 = Z_to_bv 64 t /\ getr R 9 = Z_to_bv 64 v /\
  getr R 18 = Z_to_bv 64 d /\ getr R 19 = Z_to_bv 64 pretty.

Definition tv_lr (R : bvmap 5 word) (gp tp : word) (S t v d pretty i : Z) : Prop :=
  tv_lr0 R gp tp S t v d pretty /\ getr R 20 = Z_to_bv 64 (d + 1) /\
  getr R 21 = Z_to_bv 64 0x1035c /\ getr R 22 = Z_to_bv 64 0x102aa /\ getr R 23 = Z_to_bv 64 0x10335 /\
  getr R 24 = Z_to_bv 64 (8 * i) /\ getr R 25 = Z_to_bv 64 (56 * i) /\ getr R 26 = Z_to_bv 64 i /\
  getr R 27 = Z_to_bv 64 6.

Definition tv_rng (S t v d pretty i : Z) : Prop :=
  0x40000 <= S + -112 /\ S <= 2 ^ 63 /\ 0 <= t < 2 ^ 64 /\ 0 <= v /\ v + 56 <= 2 ^ 64 /\
  0 <= d <= 2 ^ 31 - 2 /\ - 2 ^ 31 <= pretty < 2 ^ 31 /\ 0 <= i < 2 ^ 54.

Definition tv_out (pc : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (P : bvmap 5 word -> Prop)
    (ms : machine_state) : Prop :=
  exists R', ms = MS R' F (Z_to_bv 64 pc) fc None m (seg_rom rsegs) /\ P R'.

Lemma tv_out_kb : forall pc m F fc P ms, evt rsegs (tv_out pc m F fc P) ms ->
  evt rsegs (fun ms => exists R pc' mem', ms = MS R F pc' fc None mem' (seg_rom rsegs) /\
    (pc' = Z_to_bv 64 pc /\ mem' = m /\ P R)) ms.
Proof.
  intros pc m F fc P ms H. eapply evt_mono; [exact H|].
  intros s (R & -> & HP). exists R, (Z_to_bv 64 pc), m. split; [reflexivity|]. auto.
Qed.

Ltac tv_open0 L0 :=
  let E2 := fresh in let E3 := fresh in let E4 := fresh in let E8 := fresh in let E9 := fresh in
  let E18 := fresh in let E19 := fresh in
  destruct L0 as (E2 & E3 & E4 & E8 & E9 & E18 & E19);
  rewrite E2, E3, E4, E8, E9, E18, E19.

Ltac tv_open LR RG :=
  unfold rmk;
  let L0 := fresh in
  let E20 := fresh in let E21 := fresh in let E22 := fresh in
  let E23 := fresh in let E24 := fresh in let E25 := fresh in let E26 := fresh in let E27 := fresh in
  destruct LR as (L0 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27);
  tv_open0 L0;
  rewrite E20, E21, E22, E23, E24, E25, E26, E27;
  destruct RG as (? & ? & ? & ? & ? & ? & ? & ?).

Ltac tv_done :=
  apply evt_done; unfold tv_out; eexists; split; [reflexivity|];
  unfold tv_lr, tv_lr0; repeat split; tv_gv.

Lemma tv_pz : forall pretty, - 2 ^ 31 <= pretty < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 pretty) (Z_to_bv 64 0) = (pretty =? 0).
Proof.
  intros pretty Hp. destruct (Z.eq_dec pretty 0) as [->|Hn]; [reflexivity|].
  rewrite tv_ne0 by lia. symmetry. apply Z.eqb_neq. exact Hn.
Qed.

Lemma tv_seg_h0 : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty,
  tv_lr R gp tp S t v d pretty 0 -> tv_rng S t v d pretty 0 ->
  evt rsegs (tv_out 0x150a0 m F fc (fun R' => tv_lr R' gp tp S t v d pretty 0))
    (MS (rmk R) F (Z_to_bv 64 0x1508c) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty LR RG. tv_open LR RG.
  tv_until 0x150a0. tv_done.
Qed.

Lemma tv_seg_h1 : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> 0 < i ->
  evt rsegs (tv_out 0x14f08 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x150a0 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 0x10335 /\
      getr R' 12 = Z_to_bv 64 1))
    (MS (rmk R) F (Z_to_bv 64 0x1508c) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i LR RG Hi. tv_open LR RG.
  tv_until 0x14f08. tv_done.
Qed.

Lemma tv_seg_line : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> pretty <> 0 ->
  evt rsegs (tv_out 0x153e8 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x150b0 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 (d + 1)))
    (MS (rmk R) F (Z_to_bv 64 0x150a0) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i LR RG Hp. tv_open LR RG.
  pose proof (tv_ne0 pretty ltac:(lia) Hp) as HP0.
  tv_until 0x153e8. tv_done.
Qed.

Lemma tv_seg_key : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i pc0 keys x,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i ->
  pc0 = 0x150b0 \/ (pc0 = 0x150a0 /\ pretty = 0) ->
  0 <= keys -> keys + 8 * i + 8 <= 2 ^ 64 ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 6)) -> bytes_at rsegs m (v + 32) (le8 (Z_to_bv 64 keys)) ->
  bytes_at rsegs m (keys + 8 * i) (le8 (Z_to_bv 64 x)) ->
  evt rsegs (tv_out 0x1525c m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x150cc /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 x))
    (MS (rmk R) F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i pc0 keys x LR RG Hpc Hk0 Hk1 TY KS KX.
  apply tv_roc4 in TY. apply tv_roc8 in KS.
  assert (RX : ov_read_bytes rsegs m (wa (keys + 8 * i)) 8 = Some (le8 (Z_to_bv 64 x))).
  { pose proof (tv_roc8 _ _ _ KX) as C.
    pose proof (ro_cells_read_at rsegs m (keys + 8 * i) [C8 (Z_to_bv 64 x)] 0 (C8 (Z_to_bv 64 x)) 8 _ C
             eq_refl eq_refl eq_refl) as R0.
    cbn [Z.of_nat] in R0. rewrite Z.add_0_r in R0. exact R0. }
  clear KX. tv_open LR RG.
  destruct Hpc as [->|[-> ->]]; tv_until 0x1525c; tv_done.
Qed.

Lemma tv_seg_colon : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i ->
  evt rsegs (tv_out 0x14f08 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x150dc /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 0x1035c /\
      getr R' 12 = Z_to_bv 64 1))
    (MS (rmk R) F (Z_to_bv 64 0x150cc) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i LR RG. tv_open LR RG.
  tv_until 0x14f08. tv_done.
Qed.

Lemma tv_seg_sp : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> pretty <> 0 ->
  evt rsegs (tv_out 0x14f08 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x150f0 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 0x102aa /\
      getr R' 12 = Z_to_bv 64 1))
    (MS (rmk R) F (Z_to_bv 64 0x150dc) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i LR RG Hp. tv_open LR RG.
  pose proof (tv_ne0 pretty ltac:(lia) Hp) as HP0.
  tv_until 0x14f08. tv_done.
Qed.

Lemma tv_seg_kid : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i pc0 ty kids,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i ->
  pc0 = 0x150f0 \/ (pc0 = 0x150dc /\ pretty = 0) \/ (pc0 = 0x150b0 /\ ty = 5) \/
    (pc0 = 0x150a0 /\ pretty = 0 /\ ty = 5) ->
  0 <= ty < 2 ^ 31 -> 0 <= kids -> kids + 56 * i + 56 <= 2 ^ 64 ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 ty)) -> bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 kids)) ->
  evt rsegs (tv_out 0x14fc0 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x15108 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 (kids + 56 * i) /\
      getr R' 12 = Z_to_bv 64 pretty /\ getr R' 13 = Z_to_bv 64 (d + 1)))
    (MS (rmk R) F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i pc0 ty kids LR RG Hpc Hty Hk0 Hk1 TY KD.
  apply tv_roc4 in TY. apply tv_roc8 in KD. tv_open LR RG.
  destruct Hpc as [->|[[-> ->]|[[-> ->]|(-> & -> & ->)]]]; tv_until 0x14fc0; tv_done.
Qed.

Lemma tv_seg_next : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i n,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> i + 1 < n < 2 ^ 54 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  evt rsegs (tv_out 0x1508c m F fc (fun R' => tv_lr R' gp tp S t v d pretty (i + 1)))
    (MS (rmk R) F (Z_to_bv 64 0x15108) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i n LR RG Hn NN.
  apply tv_roc8 in NN. tv_open LR RG.
  tv_until 0x1508c. tv_done.
Qed.

Lemma tv_seg_endl : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i n,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> n = i + 1 -> n < 2 ^ 54 -> pretty <> 0 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  evt rsegs (tv_out 0x153e8 m F fc (fun R' => tv_lr0 R' gp tp S t v d pretty /\
      getr R' 1 = Z_to_bv 64 0x15130 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 d))
    (MS (rmk R) F (Z_to_bv 64 0x15108) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i n LR RG Hn Hn1 Hp NN.
  apply tv_roc8 in NN. tv_open LR RG.
  pose proof (tv_ne0 pretty ltac:(lia) Hp) as HP0.
  subst n. tv_until 0x153e8. tv_done.
Qed.

Definition tv_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j : list byte) : list cell :=
  [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition tv_restored (R' : bvmap 5 word) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (S : Z) : Prop :=
  getr R' 1 = ra /\ getr R' 2 = Z_to_bv 64 S /\ getr R' 3 = gp /\ getr R' 4 = tp /\
  getr R' 8 = s0 /\ getr R' 9 = s1 /\ getr R' 18 = s2 /\ getr R' 19 = s3 /\ getr R' 20 = s4 /\
  getr R' 21 = s5 /\ getr R' 22 = s6 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\
  getr R' 26 = s10 /\ getr R' 27 = s11.

Lemma tv_seg_close : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty pc0 ty n
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j : list byte),
  tv_lr0 R gp tp S t v d pretty -> tv_rng S t v d pretty 0 ->
  pc0 = 0x15130 \/ (pc0 = 0x15058 /\ n = 0) \/
    (pc0 = 0x15108 /\ pretty = 0 /\ 0 < n < 2 ^ 54 /\ getr R 26 = Z_to_bv 64 (n - 1) /\
     getr R 24 = Z_to_bv 64 (8 * (n - 1)) /\ getr R 25 = Z_to_bv 64 (56 * (n - 1))) ->
  ty = 5 \/ ty = 6 -> 0 <= n < 2 ^ 64 ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 ty)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  ro_cells rsegs m (S + -112) (tv_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  evt rsegs (tv_out 0x14f08 m F fc (fun R' => tv_restored R' ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S /\
      getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 (if ty =? 6 then 0x102a8 else 0x10390) /\
      getr R' 12 = Z_to_bv 64 1))
    (MS (rmk R) F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty pc0 ty n ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j L0 RG Hpc Hty Hn TY NN FR.
  apply tv_roc4 in TY. apply tv_roc8 in NN. unfold tv_frame in FR. unfold rmk. tv_open0 L0.
  destruct RG as (? & ? & ? & ? & ? & ? & ? & ?).
  destruct Hpc as [->|[[-> ->]|(-> & -> & Hn' & E26 & E24 & E25)]];
    [| | rewrite E26, E24, E25];
    destruct Hty as [->| ->]; tv_until 0x14f08;
    (apply evt_done; unfold tv_out; tv_fixS; eexists; split; [reflexivity|];
     unfold tv_restored; repeat split; tv_gv).
Qed.

Lemma tv_seg_after_open : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty n,
  tv_lr0 R gp tp S t v d pretty -> tv_rng S t v d pretty 0 -> 0 < n < 2 ^ 54 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  evt rsegs (tv_out 0x1508c m F fc (fun R' => tv_lr R' gp tp S t v d pretty 0))
    (MS (rmk R) F (Z_to_bv 64 0x15058) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty n L0 RG Hn NN.
  apply tv_roc8 in NN. unfold rmk. tv_open0 L0.
  destruct RG as (? & ? & ? & ? & ? & ? & ? & ?).
  tv_until 0x1508c. tv_done.
Qed.
