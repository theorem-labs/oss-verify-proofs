From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TvSeg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition tv_lr0 (R : bvmap 5 word) (gp tp : word) (S t v d pretty : Z) : Prop :=
  getr R 2 = Z_to_bv 64 (S + -128) /\ getr R 3 = gp /\ getr R 4 = tp /\
  getr R 8 = Z_to_bv 64 t /\ getr R 9 = Z_to_bv 64 v /\ getr R 19 = Z_to_bv 64 pretty.

Definition tv_lr (R : bvmap 5 word) (gp tp : word) (S t v d pretty i : Z) : Prop :=
  tv_lr0 R gp tp S t v d pretty /\ getr R 18 = Z_to_bv 64 56 /\ getr R 20 = Z_to_bv 64 (d + 1) /\
  getr R 21 = Z_to_bv 64 0x1035c /\ getr R 22 = Z_to_bv 64 0 /\ getr R 23 = Z_to_bv 64 0x10335 /\
  getr R 24 = Z_to_bv 64 (56 * i) /\ getr R 25 = Z_to_bv 64 (8 * i) /\ getr R 26 = Z_to_bv 64 i /\
  getr R 27 = Z_to_bv 64 6.

Definition tv_rng (S t v d pretty i : Z) : Prop :=
  0x40000 <= S + -128 /\ S <= 2 ^ 63 /\ 0 <= t < 2 ^ 64 /\ 0 <= v /\ v + 56 <= 2 ^ 64 /\
  0 <= d <= 2 ^ 31 - 2 /\ - 2 ^ 31 <= pretty < 2 ^ 31 /\ 0 <= i < 2 ^ 54.

Definition tv_out (pc : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (P : bvmap 5 word -> Prop)
    (ms : machine_state) : Prop :=
  exists R', ms = MS R' F (Z_to_bv 64 pc) fc None m (seg_rom rsegs) /\ P R'.

Ltac tv_open0 L0 :=
  let E2 := fresh in let E3 := fresh in let E4 := fresh in let E8 := fresh in let E9 := fresh in
  let E19 := fresh in
  destruct L0 as (E2 & E3 & E4 & E8 & E9 & E19);
  rewrite E2, E3, E4, E8, E9, E19.

Ltac tv_open LR RG :=
  unfold rmk;
  let L0 := fresh in
  let E18 := fresh in let E20 := fresh in let E21 := fresh in let E22 := fresh in
  let E23 := fresh in let E24 := fresh in let E25 := fresh in let E26 := fresh in let E27 := fresh in
  destruct LR as (L0 & E18 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27);
  tv_open0 L0;
  rewrite E18, E20, E21, E22, E23, E24, E25, E26, E27;
  destruct RG as (? & ? & ? & ? & ? & ? & ? & ?).

Ltac tv_done :=
  apply evt_done; unfold tv_out; eexists; split; [reflexivity|];
  unfold tv_lr, tv_lr0; repeat split; ub_gv.

Lemma ub_kid_a0 : forall i, 0 <= i < 2 ^ 54 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 i) ≪ 6)) -
              bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 i) ≪ 3))) = Z_to_bv 64 (56 * i).
Proof.
  intros i Hi. rewrite (unsigned_lit i) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma ub_kid_a2 : forall i kids, 0 <= i < 2 ^ 54 -> 0 <= kids -> kids + 56 * i < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 i) ≪ 6)) -
              bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 i) ≪ 3)) + kids) = Z_to_bv 64 (56 * i + kids).
Proof.
  intros i kids Hi Hk Hs. rewrite (unsigned_lit i) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma ub_sltu0 : forall x, 0 < x < 2 ^ 64 -> PropExec.v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof.
  intros x Hx. unfold PropExec.v_sltu, PropExec.c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt 0 x)) by lia. reflexivity.
Qed.

Lemma ub_sltiu1 : forall x, 0 < x < 2 ^ 64 -> PropExec.v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x Hx. unfold PropExec.v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity.
Qed.

Lemma ub_mulh0 : forall i c, 0 <= i < 2 ^ 54 -> 0 <= c <= 64 ->
  Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 i) * c) 64) = Z_to_bv 64 0.
Proof.
  intros i c Hi Hc. unfold bv_signed. rewrite unsigned_lit by lia. rewrite bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by (split; [nia | change (2 ^ 64) with 18446744073709551616; nia]).
  reflexivity.
Qed.

Lemma ub_srai0 : forall x, 0 <= x < 2 ^ 63 -> Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 x)) 63) = Z_to_bv 64 0.
Proof.
  intros x Hx. unfold bv_signed. rewrite unsigned_lit by lia. rewrite bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma ub_srl60 : forall i, 0 <= i < 2 ^ 54 -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 i) ≫ 60) = Z_to_bv 64 0.
Proof. intros i Hi. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

Lemma ub_addiw1 : forall d, 0 <= d <= 2 ^ 31 - 2 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 d) + 1)) = Z_to_bv 64 (d + 1).
Proof. intros d Hd. rewrite unsigned_lit by lia. rewrite ub_swrap_small by lia. reflexivity. Qed.

Lemma ub_slt0 : forall d, 0 <= d <= 2 ^ 31 - 2 -> PropExec.v_slt (Z_to_bv 64 (d + 1)) (Z_to_bv 64 d) = Z_to_bv 64 0.
Proof.
  intros d Hd. unfold PropExec.v_slt, PropExec.c_lts, bv_lts, bv_signed. rewrite !unsigned_lit by lia.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  rewrite (proj2 (Z.ltb_ge (d + 1) d)) by lia. reflexivity.
Qed.

Ltac ub_fix := rewrite ?ub_kid_a0, ?ub_kid_a2, ?ub_sltu0, ?ub_sltiu1, ?ub_mulh0, ?ub_srai0, ?ub_srl60, ?ub_addiw1,
  ?ub_slt0 by lia.

Ltac tv_until pc :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
  | |- context [Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 ?v)) 7)] =>
      rewrite (ub_land7 v) by first [lia | assumption | (Z.div_mod_to_equations; lia)]
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ub_br
  | _ => ub_fix; step
  end.

Lemma tv_seg_h0 : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty,
  tv_lr R gp tp S t v d pretty 0 -> tv_rng S t v d pretty 0 ->
  evt rsegs (tv_out 0x156ac m F fc (fun R' => tv_lr R' gp tp S t v d pretty 0))
    (MS (rmk R) F (Z_to_bv 64 0x15698) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty LR RG. tv_open LR RG.
  tv_until 0x156ac. tv_done.
Qed.

Lemma tv_seg_h1 : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> 0 < i ->
  evt rsegs (tv_out 0x154b8 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x156ac /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 0x10335 /\
      getr R' 12 = Z_to_bv 64 1))
    (MS (rmk R) F (Z_to_bv 64 0x15698) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i LR RG Hi. tv_open LR RG.
  tv_until 0x154b8. tv_done.
Qed.

Lemma tv_seg_line : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> pretty <> 0 ->
  evt rsegs (tv_out 0x15a70 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x156c0 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 (d + 1)))
    (MS (rmk R) F (Z_to_bv 64 0x156ac) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i LR RG Hp. tv_open LR RG.
  pose proof (ub_ne0 pretty ltac:(lia) Hp) as HP0.
  tv_until 0x15a70. tv_done.
Qed.

Lemma tv_seg_key : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i pc0 keys x,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i ->
  pc0 = 0x156c0 \/ (pc0 = 0x156ac /\ pretty = 0) ->
  0 < keys -> keys mod 8 = 0 -> keys + 8 * i + 8 <= 2 ^ 64 ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 6)) -> bytes_at rsegs m (v + 32) (le8 (Z_to_bv 64 keys)) ->
  bytes_at rsegs m (keys + 8 * i) (le8 (Z_to_bv 64 x)) ->
  evt rsegs (tv_out 0x158d4 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x15704 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 x))
    (MS (rmk R) F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i pc0 keys x LR RG Hpc Hk0 Hk8 Hk1 TY KS KX.
  apply ub_roc4 in TY. apply ub_roc8 in KS.
  assert (RX : ov_read_bytes rsegs m (wa (keys + 8 * i)) 8 = Some (le8 (Z_to_bv 64 x))).
  { pose proof (ub_roc8 _ _ _ KX) as C.
    pose proof (ro_cells_read_at rsegs m (keys + 8 * i) [C8 (Z_to_bv 64 x)] 0 (C8 (Z_to_bv 64 x)) 8 _ C
             eq_refl eq_refl eq_refl) as R0.
    cbn [Z.of_nat] in R0. rewrite Z.add_0_r in R0. exact R0. }
  clear KX. tv_open LR RG.
  destruct Hpc as [->|[-> ->]]; tv_until 0x158d4; tv_done.
Qed.

Lemma tv_seg_colon : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i ->
  evt rsegs (tv_out 0x154b8 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x15714 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 0x1035c /\
      getr R' 12 = Z_to_bv 64 1))
    (MS (rmk R) F (Z_to_bv 64 0x15704) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i LR RG. tv_open LR RG.
  tv_until 0x154b8. tv_done.
Qed.

Definition tv_frame0 (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (d : Z) (x16 jf : list byte) : list cell :=
  [CB 8 jf; C8 (Z_to_bv 64 d); CB 8 x16; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
   C8 s1; C8 s0; C8 ra].

Definition tv_frame1 (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (d : Z) (jf : list byte) : list cell :=
  [CB 8 jf; C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 0x102aa); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
   C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma tv_seg_sp : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jf : list byte),
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> pretty <> 0 ->
  ro_cells rsegs m (S + -128) (tv_frame1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d jf) ->
  evt rsegs (tv_out 0x154b8 m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x15728 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 0x102aa /\
      getr R' 12 = Z_to_bv 64 1))
    (MS (rmk R) F (Z_to_bv 64 0x15714) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 jf LR RG Hp FR.
  unfold tv_frame1 in FR. tv_open LR RG.
  pose proof (ub_ne0 pretty ltac:(lia) Hp) as HP0.
  tv_until 0x154b8. tv_done.
Qed.

Lemma tv_seg_kid : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i pc0 ty kids,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i ->
  pc0 = 0x15728 \/ (pc0 = 0x15714 /\ pretty = 0) \/ (pc0 = 0x156c0 /\ ty = 5) \/
    (pc0 = 0x156ac /\ pretty = 0 /\ ty = 5) ->
  0 <= ty < 2 ^ 31 -> 0 < kids -> kids + 56 * i + 56 <= 2 ^ 64 ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 ty)) -> bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 kids)) ->
  evt rsegs (tv_out 0x155ac m F fc (fun R' => tv_lr R' gp tp S t v d pretty i /\
      getr R' 1 = Z_to_bv 64 0x15778 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 (kids + 56 * i) /\
      getr R' 12 = Z_to_bv 64 pretty /\ getr R' 13 = Z_to_bv 64 (d + 1)))
    (MS (rmk R) F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i pc0 ty kids LR RG Hpc Hty Hk0 Hk1 TY KD.
  apply ub_roc4 in TY. apply ub_roc8 in KD. tv_open LR RG.
  destruct Hpc as [->|[[-> ->]|[[-> ->]|(-> & -> & ->)]]]; tv_until 0x155ac; tv_done.
Qed.

Lemma tv_seg_next : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i n,
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> i + 1 < n < 2 ^ 54 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  evt rsegs (tv_out 0x15698 m F fc (fun R' => tv_lr R' gp tp S t v d pretty (i + 1)))
    (MS (rmk R) F (Z_to_bv 64 0x15778) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i n LR RG Hn NN.
  apply ub_roc8 in NN. tv_open LR RG.
  tv_until 0x15698. tv_done.
Qed.

Lemma tv_seg_endl : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty i n
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jf : list byte),
  tv_lr R gp tp S t v d pretty i -> tv_rng S t v d pretty i -> n = i + 1 -> n < 2 ^ 54 -> pretty <> 0 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  ro_cells rsegs m (S + -128) (tv_frame1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d jf) ->
  evt rsegs (tv_out 0x15a70 m F fc (fun R' => tv_lr0 R' gp tp S t v d pretty /\
      getr R' 1 = Z_to_bv 64 0x157a4 /\ getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 d))
    (MS (rmk R) F (Z_to_bv 64 0x15778) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty i n ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 jf LR RG Hn Hn1 Hp NN FR.
  apply ub_roc8 in NN. unfold tv_frame1 in FR. tv_open LR RG.
  pose proof (ub_ne0 pretty ltac:(lia) Hp) as HP0.
  subst n. tv_until 0x15a70.
  apply evt_done; unfold tv_out; eexists; split; [reflexivity|].
  unfold tv_lr0; repeat split; ub_gv.
Qed.

Definition tv_restored (R' : bvmap 5 word) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (S : Z) : Prop :=
  getr R' 1 = ra /\ getr R' 2 = Z_to_bv 64 S /\ getr R' 3 = gp /\ getr R' 4 = tp /\
  getr R' 8 = s0 /\ getr R' 9 = s1 /\ getr R' 18 = s2 /\ getr R' 19 = s3 /\ getr R' 20 = s4 /\
  getr R' 21 = s5 /\ getr R' 22 = s6 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\
  getr R' 26 = s10 /\ getr R' 27 = s11.

Lemma tv_seg_close : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty pc0 ty n
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x16 j : list byte),
  tv_lr0 R gp tp S t v d pretty -> tv_rng S t v d pretty 0 ->
  pc0 = 0x157a4 \/ (pc0 = 0x15654 /\ n = 0 /\ getr R 18 = Z_to_bv 64 1) \/
    (pc0 = 0x15778 /\ pretty = 0 /\ 0 < n < 2 ^ 54 /\ getr R 26 = Z_to_bv 64 (n - 1) /\
     getr R 24 = Z_to_bv 64 (56 * (n - 1)) /\ getr R 25 = Z_to_bv 64 (8 * (n - 1))) ->
  ty = 5 \/ ty = 6 -> 0 <= n < 2 ^ 64 ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 ty)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  ro_cells rsegs m (S + -128) (tv_frame0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d x16 j) ->
  evt rsegs (tv_out 0x154b8 m F fc (fun R' => tv_restored R' ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S /\
      getr R' 10 = Z_to_bv 64 t /\ getr R' 11 = Z_to_bv 64 (if ty =? 6 then 0x102a8 else 0x10390) /\
      getr R' 12 = Z_to_bv 64 1))
    (MS (rmk R) F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty pc0 ty n ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x16 j L0 RG Hpc Hty Hn TY NN FR.
  apply ub_roc4 in TY. apply ub_roc8 in NN. unfold tv_frame0 in FR. unfold rmk. tv_open0 L0.
  destruct RG as (? & ? & ? & ? & ? & ? & ? & ?).
  destruct Hpc as [->|[(-> & -> & E18)|(-> & -> & Hn' & E26 & E24 & E25)]];
    [| rewrite E18 | rewrite E26, E24, E25];
    destruct Hty as [->| ->]; tv_until 0x154b8;
    (apply evt_done; unfold tv_out; ub_fixS; eexists; split; [reflexivity|];
     unfold tv_restored; repeat split; ub_gv).
Qed.

Definition tv_out_m (pc : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (lo hi : Z)
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists R' m', ms = MS R' F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs) /\
    munch [(lo, hi)] m m' /\ wmono rsegs m m' /\ P R' m'.

Lemma tv_seg_after_open : forall (R : bvmap 5 word) gp tp (F : bvmap 5 word) (fc : bv 32) m S t v d pretty n
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x16 jf : list byte),
  tv_lr0 R gp tp S t v d pretty -> tv_rng S t v d pretty 0 -> 0 < n < 2 ^ 54 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  rw_cells rsegs m (S + -128) (tv_frame0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d x16 jf) ->
  evt rsegs (tv_out_m 0x15698 m F fc (S + -112) (S + -104) (fun R' m' =>
      tv_lr R' gp tp S t v d pretty 0 /\
      rw_cells rsegs m' (S + -128) (tv_frame1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d jf)))
    (MS (rmk R) F (Z_to_bv 64 0x15654) fc None m (seg_rom rsegs)).
Proof.
  intros R gp tp F fc m S t v d pretty n ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x16 jf L0 RG Hn NN FR.
  apply ub_roc8 in NN. unfold tv_frame0 in FR. unfold rmk. tv_open0 L0.
  destruct RG as (? & ? & ? & ? & ? & ? & ? & ?).
  assert (HM : munch [(S + -112, S + -104)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  tv_until 0x15698. ub_fix.
  apply evt_done; unfold tv_out_m; do 2 eexists; split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [unfold tv_lr, tv_lr0; repeat split; ub_gv|].
  unfold tv_frame1. eassumption.
Qed.
